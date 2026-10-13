import os
import sys
import tempfile
import sqlite3
import subprocess
import shutil
import hashlib
import hmac
import secrets
import logging
from datetime import datetime, timedelta
from fpdf import FPDF
import customtkinter as ctk
import json
import gzip
import math
import re
import unicodedata
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import pandas as pd

def _pip_install(pkg):
    """Installe un module manquant (version Python normale uniquement).
    Dans la version installee (.exe), sys.executable est le logiciel lui-meme : on ne lance jamais pip."""
    if getattr(sys, "frozen", False):
        raise ImportError(f"Module '{pkg}' absent de cette version installee")
    subprocess.check_call([sys.executable, "-m", "pip", "install", pkg])

# Import ou installation automatique de tkcalendar
try:
    from tkcalendar import DateEntry
except ImportError:
    _pip_install("tkcalendar")
    from tkcalendar import DateEntry

# Modules du logiciel (a garder dans le MEME dossier que app.py)
from ofppt_core import (
    BASE_DIR, APP_DATA_DIR, ANALYSIS_SETTINGS_FILE, INITIAL_PASSWORD_FILE, EMPLOI_FILE, ETAB_DEFAULTS, ETAB_LABELS,
    logger, get_db_connection, atomic_write_json, backup_data, latest_backup, clean_str,
    get_admin_credentials, save_admin_credentials, _hash_password, _verify_password,
    parse_money, format_money, mois_fr, bulletin_create_sql, fetch_bulletin, migrate_bulletin_money,
    get_etab, save_etab, login_wait_seconds, login_failed, login_succeeded, password_needs_upgrade,
    temp_pdf_path, purge_temp_pdfs,
)
from ofppt_timetable import (
    TT_DAYS, TT_Q, TT_LW, TT_HH, TT_QW, TT_RH, TT_GREEN, TT_BLUE, TT_GREY, TT_ORANGE, TT_ETAB, TT_SCHEMA, TT_KIND,
    TT_PALETTE, tt_color, tt_read_file, tt_norm, tt_absents, tt_qt, tt_dur_txt, tt_blank, tt_migrate, tt_get,
    tt_fname, tt_conflict, tt_seance_text, tt_enote_load, tt_enote_apply, tt_split_name,
    tt_load_emploi, tt_analyse, tt_analyse_excel,
)
# Impression des emplois du temps au format OFPPT (mise en page + couleurs des salles)
from ofppt_timetable_pdf import tt_pdf_emploi

# --- DEUX EMPLOIS DU TEMPS : etabli par le directeur / etabli d'apres eNote ---
ENOTE_EMPLOI_FILE = os.path.join(os.path.dirname(EMPLOI_FILE), "emploi_enote.json")

# --- COULEUR UNIQUE DE L'APPLICATION ---
# Ecran de connexion : False = le logiciel s'ouvre directement, sans mot de passe.
# Remettre True pour reactiver la demande de mot de passe.
REQUIRE_LOGIN = False

MAIN_COLOR = "#0056b3" # Bleu corporatif moderne
MAIN_COLOR_HOVER = "#003d82"

# --- MOTIFS D'ABSENCE (Suivi d'absence + emploi du temps) ---
ABS_MOTIFS = [
    "Maladie", "Une autorisation", "Formation", "Sans justif",
    "Congé annuel", "Congé de maternité / paternité", "Congé exceptionnel (décès, mariage...)",
    "Mission / Déplacement", "Examen / Concours", "Réunion / Séminaire", "Grève", "Autre",
]

def absence_multi(motif):
    """Vrai si le motif peut couvrir plusieurs jours (date de fin) ; 'Une autorisation' et 'Sans justif' = 1 jour."""
    return str(motif or "") not in ("Une autorisation", "Sans justif")

# Configuration du thème graphique
ctk.set_appearance_mode("System")
ctk.set_default_color_theme("blue")

# --- GRANDES VILLES DU MAROC (liste deroulante du champ "Lieu" des formations) ---
MOROCCO_CITIES = [
    "Casablanca", "Rabat", "Fès", "Marrakech", "Tanger", "Agadir", "Meknès", "Oujda", "Kénitra",
    "Tétouan", "Salé", "Témara", "Nador", "Safi", "El Jadida", "Béni Mellal", "Mohammedia",
    "Khouribga", "Settat", "Berrechid", "Taza", "Khémisset", "Larache", "Ksar El Kébir",
    "Guelmim", "Laâyoune", "Dakhla", "Errachidia", "Ouarzazate", "Essaouira", "Al Hoceïma",
    "Berkane", "Taourirt", "Guercif", "Taroudant", "Inezgane", "Khénifra", "Ifrane", "Azrou",
    "Midelt", "Chefchaouen", "Asilah", "Sidi Kacem", "Sidi Slimane", "Youssoufia", "Oued Zem",
    "Fquih Ben Salah", "Tan-Tan", "Smara", "Zagora", "Tinghir", "Azilal", "Benslimane",
    "Skhirat", "Martil", "Tiflet", "Bouznika", "Ben Guerir", "Mhamid", "Figuig", "Jerada",
]

# ------------------------------------------------------------------
# IMPORT DES FORMATIONS DEPUIS UN PDF / EXCEL (filtre sur le personnel de l'ISTA)
# ------------------------------------------------------------------
import threading
import queue
import difflib
import concurrent.futures


def _fnorm(s):
    """Minuscules, sans accents ni ponctuation (pour comparer des noms)."""
    s = unicodedata.normalize("NFD", str(s or ""))
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()

_ISO_RE = re.compile(r"(\d{4})-(\d{2})-(\d{2})")
_DATE_RE = re.compile(r"(\d{1,2})\s*[/\-.]\s*(\d{1,2})\s*[/\-.]\s*(\d{4}|\d{2})")

def _cell_txt(v):
    try:
        if v is None or (not isinstance(v, str) and pd.isna(v)):
            return ""
    except Exception:
        pass
    if isinstance(v, (datetime, pd.Timestamp)):
        return v.strftime("%d/%m/%Y")
    if isinstance(v, float) and v.is_integer():
        return str(int(v))
    return re.sub(r"\s+", " ", str(v)).strip()

def _dates_in(text):
    """Toutes les dates (jj/mm/aaaa, jj-mm-aa, aaaa-mm-jj) d'un texte, dans l'ordre."""
    text = str(text or "")
    found = []
    for m in _ISO_RE.finditer(text):
        try:
            found.append((m.start(), datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)))))
        except ValueError:
            pass
    text2 = _ISO_RE.sub(lambda m: " " * len(m.group(0)), text)
    for m in _DATE_RE.finditer(text2):
        d, mo, y = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if y < 100:
            y += 2000
        try:
            found.append((m.start(), datetime(y, mo, d)))
        except ValueError:
            pass
    found.sort(key=lambda t: t[0])
    return [d for _p, d in found]

def _boxes_to_lines(items):
    """items : (x, y_centre, hauteur, texte) -> lignes de texte (tri par y puis x)."""
    if not items:
        return []
    hs = sorted(i[2] for i in items)
    mh = hs[len(hs) // 2] or 10
    items = sorted(items, key=lambda t: t[1])
    lines, cur, cy = [], [], 0.0
    for it in items:
        if cur and abs(it[1] - cy) > 0.6 * mh:
            lines.append(cur)
            cur = []
        cur.append(it)
        cy = sum(c[1] for c in cur) / len(cur)
    if cur:
        lines.append(cur)
    return [" ".join(t[3] for t in sorted(l, key=lambda t: t[0])) for l in lines]

def _ocr_factories():
    """Moteurs OCR possibles, dans l'ordre d'essai : Tesseract (s'il est installe), puis RapidOCR (pip)."""
    def tesseract():
        exe = shutil.which("tesseract")
        if not exe:
            for c in (r"C:\Program Files\Tesseract-OCR\tesseract.exe",
                      r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe"):
                if os.path.exists(c):
                    exe = c
                    break
        if not exe:
            raise RuntimeError("Tesseract non installe")
        try:
            import pytesseract
        except ImportError:
            _pip_install("pytesseract")
            import pytesseract
        pytesseract.pytesseract.tesseract_cmd = exe
        langs = pytesseract.get_languages(config="")
        lang = "fra" if "fra" in langs else "eng"

        def run(img):
            d = pytesseract.image_to_data(img, lang=lang, config="--psm 6", output_type=pytesseract.Output.DICT)
            items = []
            for k, t in enumerate(d["text"]):
                if t and t.strip() and float(d["conf"][k]) >= 0:
                    items.append((d["left"][k], d["top"][k] + d["height"][k] / 2.0, d["height"][k], t.strip()))
            return _boxes_to_lines(items)
        return run, 4

    def rapid():
        try:
            from rapidocr_onnxruntime import RapidOCR
        except ImportError:
            _pip_install("rapidocr-onnxruntime")
            from rapidocr_onnxruntime import RapidOCR
        import numpy as np
        eng = RapidOCR()

        def run(img):
            if img.width > 1400:                      # image reduite : lecture bien plus rapide
                r = 1400.0 / img.width
                img = img.resize((1400, int(img.height * r)))
            res, _ = eng(np.array(img.convert("RGB")))
            items = []
            for box, text, _score in (res or []):
                xs = [p[0] for p in box]
                ys = [p[1] for p in box]
                items.append((min(xs), (min(ys) + max(ys)) / 2.0, max(ys) - min(ys), str(text).strip()))
            return _boxes_to_lines(items)
        return run, 1

    return [tesseract, rapid]

def _ocr_pdf_lines(path, progress=None):
    """OCR d'un PDF scanne (images) -> liste de lignes de texte, toutes pages. Resultat mis en cache."""
    st = os.stat(path)
    key = hashlib.sha1(f"{os.path.abspath(path)}|{st.st_size}|{int(st.st_mtime)}".encode()).hexdigest()[:16]
    cache_dir = os.path.join(APP_DATA_DIR, "ocr_cache")
    cache = os.path.join(cache_dir, key + ".json")
    if os.path.exists(cache):
        try:
            with open(cache, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            logger.warning("Cache OCR illisible, relance de la lecture", exc_info=True)
    try:
        import pdfplumber
    except ImportError:
        raise RuntimeError("Lecture d'un PDF scanne impossible : installez pdfplumber (pip install pdfplumber).")

    errs, all_lines = [], []
    with pdfplumber.open(path) as pdf:
        n = len(pdf.pages)
        if progress:
            progress(-1, n)                           # preparation du moteur (installation la 1re fois)
        run, workers, img0 = None, 1, pdf.pages[0].to_image(resolution=200).original.convert("L")
        first = None
        for f in _ocr_factories():
            try:
                run, workers = f()
                first = run(img0)                     # test du moteur sur la 1re page
                break
            except Exception as ex:
                logger.warning("Moteur OCR indisponible : %s", ex)
                errs.append(str(ex))
                run = None
        if run is None:
            raise RuntimeError(
                "PDF scanne : aucun moteur OCR disponible.\n"
                "Installez Tesseract (https://github.com/UB-Mannheim/tesseract/wiki, avec le français) "
                "ou laissez le logiciel installer RapidOCR (connexion internet requise).\n\n"
                + " | ".join(errs[-2:]))
        workers = max(1, min(workers, os.cpu_count() or 1))
        results = {0: first}
        if progress:
            progress(1, n)
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            futs = {}
            for i in range(1, n):
                img = pdf.pages[i].to_image(resolution=200).original.convert("L")
                futs[i] = ex.submit(run, img)
            for k, i in enumerate(sorted(futs), start=2):
                results[i] = futs[i].result()
                if progress:
                    progress(k, n)
        for i in range(n):
            all_lines += results[i]
    if progress:
        progress(n, n)
    try:
        os.makedirs(cache_dir, exist_ok=True)
        with open(cache, "w", encoding="utf-8") as f:
            json.dump(all_lines, f, ensure_ascii=False)
    except Exception:
        logger.warning("Ecriture du cache OCR impossible", exc_info=True)
    return all_lines

_NUMC = "0-9OoIil!S"
_PER_RE = re.compile(r"[DO][uU0o][\s.]*([%s]{1,3})[\s.]*(?:au)?[\s.]*([%s]{1,3})\s*[/.\-]\s*([%s]{1,2})\s*[/.\-]\s*(\d{4})"
                     % (_NUMC, _NUMC, _NUMC))
_MODE_RE = re.compile(r"\b(pr\w{1,3}sent\w*|\w{0,2}\s?distance)\b", re.I)
_PLAN_BLACK = re.compile(r"ofppt|office|promotion du travail|objet|liste des|intersection|\btel\b|\bfax\b|\bmode\b|"
                         r"p.riode|lieu de|plan de formation|formateurs|n°|presence", re.I)

def _digits(s):
    """Lit un nombre abime par l'OCR (O->0, l/I/i/!->1, S->5) ; garde les 2 derniers chiffres."""
    t = "".join({"O": "0", "o": "0", "I": "1", "i": "1", "l": "1", "!": "1", "S": "5"}.get(c, c) for c in str(s))
    t = "".join(c for c in t if c.isdigit())
    return int(t[-2:]) if t else None

def _period_dates(m):
    """'Du 30 au 02/12/2026' -> (30/11/2026, 02/12/2026) ; le mois de debut recule si jour debut > jour fin."""
    d1, d2, mo, y = _digits(m.group(1)), _digits(m.group(2)), _digits(m.group(3)), int(m.group(4))
    if not d1 or not d2 or not mo:
        return None
    try:
        fin = datetime(y, mo, d2)
    except ValueError:
        return None
    smo, sy = (mo, y) if d1 <= d2 else ((mo - 1, y) if mo > 1 else (12, y - 1))
    try:
        deb = datetime(sy, smo, d1)
    except ValueError:
        deb = fin
    return deb, fin

def _clean_lieu(s):
    s = re.sub(r"^[^A-Za-zÀ-ÿ]+", "", str(s or ""))
    s = re.sub(r"[^A-Za-z0-9À-ÿ.)]+$", "", s).strip()
    # corrige les fautes de lecture d'un nom de ville connu (ex. OUIDA -> OUJDA)
    mots = {w for c in MOROCCO_CITIES for w in _fnorm(c).split() if len(w) >= 5}
    out = []
    for tok in s.split():
        n = _fnorm(tok)
        if len(n) >= 5 and n not in mots:
            best = difflib.get_close_matches(n, mots, 1, 0.8)
            if best:
                tok = best[0].upper() if tok.isupper() else best[0].capitalize()
        out.append(tok)
    return " ".join(out)

def _plan_to_table(lines):
    """Reconnait un 'Plan de formation' OFPPT (liste des themes numerotes + liste des formateurs par N° de theme)
    et le transforme en tableau : Matricule | Formateur | Theme | Lieu | Date debut | Date fin. None sinon."""
    lines = [re.sub(r"\s+", " ", str(l).replace("|", " ")).strip() for l in lines]
    lines = [l for l in lines if l]
    cut = next((i for i, l in enumerate(lines) if re.search(r"liste\s+des\s+formateurs\s+participants", l, re.I)), None)
    theme_lines = lines[:cut] if cut is not None else lines

    labels, periods, pending, last = {}, [], [], 0
    for i, ln in enumerate(theme_lines):
        pm = _PER_RE.search(ln)
        if pm:
            d = _period_dates(pm)
            if d:
                periods.append((i, d[0], d[1], _clean_lieu(ln[pm.end():])))
        head = ln[:pm.start()] if pm else ln
        m = re.match(r"^(\d{1,2})\s+(\D.*)$", head.strip())
        if m and last < int(m.group(1)) <= last + 2:
            n, title = int(m.group(1)), m.group(2)
            mm = _MODE_RE.search(title)
            remote = bool(mm and "distance" in mm.group(0).lower()) or bool("distance" in ln.lower())
            if mm:
                title = title[:mm.start()]
            title = " ".join(pending[-1:] + [title.strip()]).strip()
            title = re.sub(r"^[^A-Za-zÀ-ÿ0-9]+|[^A-Za-zÀ-ÿ0-9)]+$", "", title)
            title = re.sub(r"(fiscalit[ée]\s*-\s*)(15|1S|I5|S)$", r"\1IS", title, flags=re.I)
            labels[n] = (i, title, remote)
            pending, last = [], n
        elif pm or _PLAN_BLACK.search(ln):
            pending = []
        elif len(ln) > 12 and sum(c.isalpha() or c == " " for c in ln) >= 0.85 * len(ln) \
                and sum(c.islower() for c in ln) >= 0.3 * sum(c.isalpha() for c in ln):
            pending = [ln]          # debut de titre sur plusieurs lignes (jamais une ligne tout en majuscules = lieu)
        else:
            pending = []
    if not labels:
        return None

    def window(n):
        lo = max([v[0] for k, v in labels.items() if k < n], default=-1)
        hi = min([v[0] for k, v in labels.items() if k > n], default=10 ** 9)
        return lo, hi

    def lieu_for(n, deb, fin):
        same = [(i, l) for i, d, f, l in periods if d == deb and f == fin and l]
        if not same:
            return ""
        if n in labels:
            lo, hi = window(n)
            win = [(i, l) for i, l in same if lo <= i <= hi]
            if win:
                return min(win, key=lambda t: abs(t[0] - labels[n][0]))[1]
        return same[0][1] if len({l for _i, l in same}) == 1 else ""

    def guess_theme(deb, fin):
        """N° illisible : on deduit le theme de la periode (label le plus proche au-dessus), si c'est sans ambiguite."""
        found = set()
        for i, d, f, _l in periods:
            if d == deb and f == fin:
                prev = [(v[0], k) for k, v in labels.items() if v[0] <= i and i - v[0] <= 10]
                if prev:
                    found.add(max(prev)[1])
        return found.pop() if len(found) == 1 else None

    rows = [["Matricule", "Formateur", "Thème", "Lieu", "Date début", "Date fin"]]
    for ln in lines:
        m = re.match(r"^(\d{4,5})\s+(.*)$", ln)
        if not m:
            continue
        rest = m.group(2)
        pm = _PER_RE.search(rest)
        d = _period_dates(pm) if pm else None
        if not d:
            continue
        before = rest[:pm.start()].strip()
        m2 = re.match(r"^(.*?)(?:^|\s)([%s]{1,2})$" % _NUMC, before)
        name, n = (m2.group(1).strip(), _digits(m2.group(2))) if m2 else (before, None)
        if n is not None and n not in labels:
            n = None
        devine = False
        if n is None:
            n = guess_theme(d[0], d[1])
            devine = n is not None
        info = labels.get(n)
        theme = (info[1] if info else "Formation (thème à préciser)") + (" (à distance)" if info and info[2] else "") \
            + (" (thème à vérifier)" if devine else "")
        lieu = lieu_for(n, d[0], d[1]) if n else ""
        rows.append([m.group(1), name, theme, lieu, d[0].strftime("%d/%m/%Y"), d[1].strftime("%d/%m/%Y")])
    return rows if len(rows) > 1 else None

def _pdf_tables(path, progress=None):
    """Lit un PDF : tableaux si possible, sinon texte, sinon OCR (PDF scanne)."""
    try:
        import pdfplumber
    except ImportError:
        try:
            _pip_install("pdfplumber")
            import pdfplumber
        except Exception:
            pdfplumber = None
    tables, lines = [], []
    if pdfplumber:
        with pdfplumber.open(path) as pdf:
            for page in pdf.pages:
                tbs = page.extract_tables()
                for tb in tbs:
                    t = [[_cell_txt(c) for c in row] for row in tb]
                    if t:
                        tables.append(t)
                if not tbs:
                    lines += [[ln.strip()] for ln in (page.extract_text() or "").splitlines() if ln.strip()]
    else:
        try:
            from pypdf import PdfReader
        except ImportError:
            raise RuntimeError("Lecture PDF impossible : installez pdfplumber (pip install pdfplumber).")
        for page in PdfReader(path).pages:
            lines += [[ln.strip()] for ln in (page.extract_text() or "").splitlines() if ln.strip()]
    if not tables and not lines:                       # PDF scanne : aucune couche de texte
        ocr = _ocr_pdf_lines(path, progress)
        plan = _plan_to_table(ocr)
        return [plan] if plan else [[[l] for l in ocr if l.strip()]]
    if lines:
        plan = _plan_to_table([r[0] for r in lines])
        tables.append(plan if plan else lines)
    return tables

def read_formation_tables(path, progress=None):
    """Retourne une liste de tableaux (chacun = liste de lignes = liste de cellules texte)."""
    ext = os.path.splitext(path)[1].lower()
    if ext in (".xlsx", ".xlsm", ".xls"):
        tables = []
        for df in pd.read_excel(path, sheet_name=None, header=None, dtype=object).values():
            tables.append([[_cell_txt(v) for v in r] for r in df.itertuples(index=False)])
    elif ext in (".csv", ".txt"):
        df = None
        for enc in ("utf-8-sig", "cp1252"):
            try:
                df = pd.read_csv(path, header=None, sep=None, engine="python", dtype=str, encoding=enc)
                break
            except UnicodeDecodeError:
                continue
        if df is None:
            raise RuntimeError("Fichier CSV illisible.")
        tables = [[[_cell_txt(v) for v in r] for r in df.itertuples(index=False)]]
    elif ext == ".pdf":
        tables = _pdf_tables(path, progress)
    else:
        raise RuntimeError("Format non pris en charge (PDF, Excel ou CSV uniquement).")
    return [[r for r in t if any(c for c in r)] for t in tables if t]

def _col_kind(cell):
    toks = _fnorm(cell).split()
    if not toks:
        return None
    s = set(toks)
    if "fin" in s or toks == ["au"]:
        return "fin"
    if "debut" in s or toks == ["du"]:
        return "debut"
    if s & {"lieu", "ville", "site", "destination"}:
        return "lieu"
    if s & {"theme", "intitule", "formation", "module", "titre", "action", "objet", "sujet", "thematique"}:
        return "theme"
    if s & {"matricule", "mle", "cin"}:
        return "mat"
    if s & {"formateur", "formatrice", "nom", "prenom", "participant", "agent", "personnel", "beneficiaire"}:
        return "nom"
    return None

def _find_header(table):
    for i, row in enumerate(table[:25]):
        kinds = {}
        for j, c in enumerate(row):
            k = _col_kind(c)
            if k:
                kinds.setdefault(k, []).append(j)
        if len(kinds) >= 2 and ("nom" in kinds or "theme" in kinds):
            return i, kinds
    return None, {}

def match_formations(tables, personnel):
    """Garde uniquement les formations du personnel enregistre (par matricule ou par nom).
    personnel : liste de (id, nom, prenom[, cin/matricule]).
    Retourne (liste de dicts, stats)."""
    pers = []
    for rec in personnel:
        pid, nom, prenom = rec[0], rec[1], rec[2]
        cin = "".join(c for c in str(rec[3] or "") if c.isdigit()) if len(rec) > 3 else ""
        need = set(_fnorm(nom).split()) | set(_fnorm(prenom).split())
        if need:
            cn, cp = _fnorm(nom).replace(" ", ""), _fnorm(prenom).replace(" ", "")

            def alt(h, cn=cn, cp=cp):
                # tolere "ELAMRANI" / "EL AMRANI", sans accepter les noms trop courts
                if len(cn) >= 4 and cn in h and (not cp or len(cp) < 3 or cp in h):
                    return True
                for tgt in (cn + cp, cp + cn):      # tolere les petites erreurs de lecture (OCR)
                    if len(tgt) >= 8 and abs(len(h) - len(tgt)) <= 4 \
                            and difflib.SequenceMatcher(None, h, tgt).ratio() >= 0.88:
                        return True
                return False
            pers.append((pid, f"{(nom or '').upper()} {prenom or ''}".strip(), need, alt, cin))
    cities = [(c, f" {_fnorm(c)} ") for c in MOROCCO_CITIES]

    out, seen = [], set()
    stats = {"lignes": 0, "ignorees": 0, "sans_date": 0}
    for table in tables:
        h_idx, kinds = _find_header(table)
        body = table[h_idx + 1:] if h_idx is not None else table
        for row in body:
            stats["lignes"] += 1

            def col(kind):
                return " ".join(row[j] for j in kinds.get(kind, []) if j < len(row)).strip()

            name_cols = kinds.get("nom")
            name_text = " ".join(row[j] for j in name_cols if j < len(row)) if name_cols else " ".join(row)
            norm_name = _fnorm(name_text)
            toks = set(norm_name.split())
            compact = norm_name.replace(" ", "")
            mat = "".join(c for c in col("mat") if c.isdigit())
            hits = [p for p in pers if (len(p[4]) >= 4 and mat and p[4] == mat) or p[2] <= toks or p[3](compact)]
            if not hits:
                stats["ignorees"] += 1
                continue

            all_text = " ".join(row)
            d1 = _dates_in(col("debut"))
            d2 = _dates_in(col("fin"))
            if d1 and d2:
                dates = [d1[0], d2[0]]
            else:
                dates = _dates_in(all_text)
            if not dates:
                stats["sans_date"] += 1
                continue
            d_deb, d_fin = dates[0], (dates[1] if len(dates) > 1 else dates[0])
            if d_deb > d_fin:
                d_deb, d_fin = d_fin, d_deb

            lieu = col("lieu")
            if not lieu and "lieu" not in kinds:
                norm_all = f" {_fnorm(all_text)} "
                lieu = next((c for c, n in cities if n in norm_all), "")
            theme = col("theme")
            if not theme:
                if len(row) > 1:
                    cand = [c for c in row if c and not _dates_in(c) and not (set(_fnorm(c).split()) & hits[0][2])
                            and _fnorm(c) != _fnorm(lieu)]
                    theme = max(cand, key=len) if cand else ""
                else:
                    t = _DATE_RE.sub(" ", _ISO_RE.sub(" ", all_text))
                    drop = set().union(*(h[2] for h in hits)) | set(_fnorm(lieu).split())
                    t = " ".join(w for w in t.split() if _fnorm(w) not in drop or not _fnorm(w))
                    theme = t
                    for _ in range(6):
                        theme = re.sub(r"^[\s\-|:;,]+|[\s\-|:;,]+$", "", theme)
                        theme = re.sub(r"\s+(du|au|le|a|à)$", "", theme, flags=re.I)
            theme = theme or "Formation (à préciser)"
            lieu = lieu or "Non précisé"

            for pid, pname, _need, _alt, _cin in hits:
                key = (pid, _fnorm(theme), d_deb.date(), d_fin.date())
                if key in seen:
                    continue
                seen.add(key)
                out.append({"p_id": pid, "p_name": pname, "theme": theme, "lieu": lieu,
                            "d_debut": d_deb, "d_fin": d_fin})
    return out, stats


# ------------------------------------------------------------------
# CLASSE GENERATEUR PDF ATTESTATION DE TRAVAIL
# ------------------------------------------------------------------
class PDF_Attestation(FPDF):
    def header(self):
        logo_png = os.path.join(BASE_DIR, "logo_ofppt.png")
        logo_jpg = os.path.join(BASE_DIR, "logo_ofppt.jpg")

        logo_w = 84
        logo_h = 24
        center_x = (210 - logo_w) / 2

        if os.path.exists(logo_png):
            self.image(logo_png, x=center_x, y=10, w=logo_w, h=logo_h)
            self.ln(26)
        elif os.path.exists(logo_jpg):
            self.image(logo_jpg, x=center_x, y=10, w=logo_w, h=logo_h)
            self.ln(26)
        else:
            self.set_font("Arial", 'B', 14)
            self.cell(0, 10, clean_str("OFPPT"), ln=True, align='C')
            self.ln(10)

        self.set_font("Arial", 'B', 13)
        self.set_text_color(100, 100, 100)
        self.cell(0, 8, clean_str(get_etab()["complexe"]), ln=True, align='C')
        self.set_text_color(0, 0, 0)
        self.ln(10)

    def footer(self):
        self.set_auto_page_break(auto=False, margin=0)

        self.set_draw_color(150, 150, 150)
        self.set_line_width(0.6)
        self.line(100, 272, 100, 287)

        self.set_font("Arial", 'B', 10)
        self.set_text_color(120, 120, 120)
        self.set_xy(10, 275)
        et = get_etab()
        self.cell(85, 5, clean_str(et["nom_court"]), align='R')

        self.set_font("Arial", 'I', 8.5)
        self.set_xy(105, 273)
        self.cell(0, 5, clean_str(et["adresse"]), align='L')

        self.set_xy(105, 279)
        self.cell(0, 5, clean_str(f"{et['tel']}   /   Fax : {et['fax']}"), align='L')

        self.set_auto_page_break(auto=True, margin=15)


# ------------------------------------------------------------------
# CLASSE GENERATEUR PDF ATTESTATION DE SALAIRE
# ------------------------------------------------------------------
class PDF_Attestation_Salaire(FPDF):
    """PDF attestation de salaire - mise en page identique au modele Word
    (A4, marges 25 mm, Calibri 11). Primitives bas niveau (text/line)
    compatibles fpdf 1.7.2 ET fpdf2 (evite l'erreur 'Not enough horizontal
    space' de cell())."""
    fam = "Arial"   # remplace par Calibri si la police est disponible (use_calibri)

    def use_calibri(self):
        """Enregistre Calibri (police du modele Word) si elle existe sur la
        machine (Windows, ou dossier du programme) ; sinon on garde Arial."""
        win = os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts")
        jeux = [
            (BASE_DIR, ("calibri.ttf", "calibrib.ttf", "calibrii.ttf", "calibriz.ttf")),
            (win, ("calibri.ttf", "calibrib.ttf", "calibrii.ttf", "calibriz.ttf")),
            ("/usr/share/fonts/truetype/crosextra",
             ("Carlito-Regular.ttf", "Carlito-Bold.ttf", "Carlito-Italic.ttf", "Carlito-BoldItalic.ttf")),
        ]
        for dossier, noms in jeux:
            chemins = [os.path.join(dossier, n) for n in noms]
            if all(os.path.exists(c) for c in chemins):
                try:
                    for st, c in zip(("", "B", "I", "BI"), chemins):
                        self.add_font("Calibri", st, c, uni=True)
                    return "Calibri"
                except Exception:
                    logger.exception("Police Calibri non chargee, retour a Arial")
        return "Arial"

    def header(self):
        logo_png = os.path.join(BASE_DIR, "logo_ofppt.png")
        logo_jpg = os.path.join(BASE_DIR, "logo_ofppt.jpg")
        try:
            if os.path.exists(logo_png):
                self.image(logo_png, x=(210 - 70) / 2, y=9, w=70)
            elif os.path.exists(logo_jpg):
                self.image(logo_jpg, x=(210 - 70) / 2, y=9, w=70)
            else:
                self._txt(105, 20, "OFPPT", 16, bold=True, align="C")
        except Exception:
            logger.warning("Logo introuvable ou illisible pour le PDF", exc_info=True)
        self._txt(105, 54, get_etab()["complexe"], 11, align="C")

    def footer(self):
        # pied de page du modele Word : "CF BERKANE" | adresse + telephone
        self.set_draw_color(0, 0, 0)
        self.set_line_width(0.9)
        self.line(108.8, 267, 108.8, 275.5)
        et = get_etab()
        self._txt(39.6, 270.4, et["nom_court"], 8, bold=True)
        self._txt(109.6, 270.4, et["adresse"], 8, italic=True)
        self._txt(109.6, 274.1, f"{et['tel']}     /     Fax : {et['fax']}", 8, italic=True)

    def _txt(self, x, y, s, size=11, bold=False, align="L", grey=False, w=None, italic=False):
        self.set_font(self.fam, ("B" if bold else "") + ("I" if italic else ""), size)
        self.set_text_color(120, 120, 120) if grey else self.set_text_color(0, 0, 0)
        s = clean_str(s)
        if align == "C":
            x = (self.w - self.get_string_width(s)) / 2
        elif align == "R" and w is not None:
            x = x + w - self.get_string_width(s)
        self.text(x, y, s)


# ------------------------------------------------------------------
# ORDRE DE MISSION - mise en page identique au modele Word
# (NOUVEAU_MODELE_ORDRE_DE_MISSION_.docx : A4, marges 25 mm / 20 mm, Times)
# Le logo du modele est integre au code (aucun fichier image a fournir).
# ------------------------------------------------------------------
OM_LOGO_B64 = (
    "iVBORw0KGgoAAAANSUhEUgAAAmcAAADVCAYAAAASL1dGAAAAAXNSR0IArs4c6QAAAARnQU1BAACxjwv8YQUAAAAJcEhZcwAAFxEA"
    "ABcRAcom8z8AAAAhdEVYdENyZWF0aW9uIFRpbWUAMjAyMjowNjowNiAxMzo1MzozN90aXIEAAHhuSURBVHhe7Z0HwBTF+f8H3l7o"
    "TUSpUgVBEXsBFRXUKKgxtlgSezQYE39qEkWjiX9LNBp7bIm9oFEBEzEiFkRAQREEBJEq/YW3N/jPd3afe2dnZ+/27r1733vf9/nA"
    "vFtudnZmdm7ne8+0VrslgmEYhmEYhkkLWrtbhmEYhmEYJg1gccYwDMMwDJNGsDhjGIZhGIZJI1icMQzDMAzDpBEszhiGYRiGYdII"
    "FmcMwzAMwzBpBIszhmEYhmGYNILFGcMwDMMwTBrB4oxhGIZhGCaNYHHGMAzDMAyTRrA4YxiGYRiGSSNYnDEMwzAMw6QRLM4YhmEY"
    "hmHSCBZnDMMwDMMwaQSLM4ZhGIZhmDSCxRnDMAzDMEwaweKMYRiGYRgmjWi1W+LuM/WgobKxVatW7h7DMAzDMM0RFmcJEC3LzM9s"
    "fs1zNsFlnosmyliwMQzDMEzzgcVZCKIJLHNL+M4bnwfiCi0SXEEiLehzYDvHMAzDMEzTgMWZBVuW4Bw5InKMrX7s7tu2sQgSX9gq"
    "5xxEjukz2tK+ju0cwzAMwzDpCYszFzMbcExOP5Z/xC533+bArl27IvtA/ywWpsBq3bp15Jg+g8N5oD53PoycM/3rmMcMwzAMw6QX"
    "LVqcmUknEUXnIbLkgUeMkfCCq62tjfijz4C5L7PZ3XrvCaFEx7qgkr4ixyTOdEfn9M88+9i6x4DO0zFhHjMMwzAM0/i0SHGmJxn7"
    "5IAutGhr7pvHGZmZUui0VgIpMyMTqkdkZGSo42i4twwE96ipqVb7tTU1UiTK+6p71iphhfBJlAXtZ8gt4oNjgHPkCH2fYRiGYZjG"
    "pUWJMz2pJK6ALrZoCwfLGO2TU4InM0uJrwwpxDKlMEuU+uQ8RFpNbY0SbbVyC8FGoowcCUQ4FW9s3X3dEfo+wzAMwzCNQ7MXZ3ry"
    "sO9xUuDUSod9El8kyLCFg2BxRFiWyM7JcUNKDvK2SaW6ukqJNWxl6K6AdASaLtSUgzBjocYwDMMwaUezFWd6spQQcx2EF211IaYL"
    "MpktIjs7R4kxCJlUoUUx6SCNVVWVokYKNVjVbEKNthBitGWRxjAMwzCNS7MTZ3pysE8O4kt3JMRqVLOgYyGDIMvKyVVWpYagoXIe"
    "6Yc1rbKiXKZTRIQaOQgz3ZkijQUawzAMwzQczUqcUVKwJWcKMogx7NO2dUamyMvLj/Qdq092KAkDUaM28q90Sui52iZy3sW5lYyn"
    "s1FgE0mHjB8d1yNaCgoTaa6sLBe1NdU+kWYKNRJoFGc97gzDMAzDpIZmIc70JEB84BhbcrqFDFt8np2dK3Jzc1W/K52w2QGh4vTb"
    "creuIyEmA8J/FR5Ou6fUtBzSp3PCRV2mHKbWoHPwgwNnS9diS+nDFsdhsKULzZ5VVRUq/hCnNqFG6cI+4cSNYRiGYZhU0OTFGUUf"
    "W12YQYiZomzXrt0iNy9fibIggrLDEWKtRQbEmHRSoajzu2WYCBfCSV4s7+WMAAU2DWOewxQcPnx+cAIiyflI3V/uIa4qvXDyviTe"
    "bASlC9RUV0uRVq72SaTRVrei0RawQGMYhmGY1NBkxRlFG1tyuyDILJYyiLWc3OiijNCzA4KsdQYEGYkSR4jVQozJsDWvCljRINZ0"
    "TA0DgbN7tybg1B9DoBnXwNJmPiR4QdiIFznEneKGeOrX6OkKwhRpHmsaRJrc4j5sRWMYhmGY1NEkxRlFGVsIL3JkLauWIkPtQ5Tl"
    "5IUSZToZUpApi5EreGpqZdg1EGPerIIFSz8FnWJ4Ued0THEGTOuZCsfdB47wcg9cTEmEaxznfAL/0Ikk1JRlLyQQtBUVpUqQmSJN"
    "5Yvr6F4s0BiGYRgmeTQpcUZRxZYcCTI4iAoSZlnZ2SIvN9/Xp8wGpAX8ZUpRRtavGinGamQ4eu6YEsQUZzZM3eJc470oljhz8AZk"
    "xsWmj9Q8ZnKr8slNk3nvaGDgQHVVlRRnTjNnRKhBnLEVjWEYhmFSQpMRZxRNbE1LmS7MIHTyCwqVlScWEBMQZGi6RNNhtQrDGTCA"
    "z8ycMaVHGHFmijGriIrRrOngPSmD9cfPvM49gb8knCDSnDzzWu+CwJJRleVlMr+l4M3KqhNoriWNBBqFT1uGYRiGYRKjSYgziiIE"
    "GfbRVAerFgQZOYiqAinKwsziDzHhWH+kkJDhVVXJMGTYPrUTQxAlIs6AqV+UdU/3ojxEj4sRhMIXrjxhhoKmWoBmTjTV1qDtM1Yi"
    "JOiPVlFZpvLNI9JUPnqtaCzQGIZhGCZx0lqcUdSUIHOFmWkpg4MoKCxsG7MJ05kyQgoJKZgg8KqqnLCAc62ZFV6RQX3QdEwhgkPd"
    "C4I1LlF+dHziDJh+1L3dA4kKI1a4uMbdJ8gLxRsiDc2dYS1p5eWlMu9qrFY0sqBR2LRlGIZhGCY8aSvOKFrYms2YJMog0PLzY1vL"
    "IBGUgMhsrSZ2rax0RnDqSVdCwqclvCdCiTNYymCN0jA1iv/YIip9frziDBhefOH6TwRd08oZ9CDzFoMHYgErGvqjYeAExBmEmi7Q"
    "SKQBFmgMwzAMEx9pKc4oSkHNmBBm8NKmTWxrWaYrynbVovnSGSwAHLGjJV0emzoCokn3k4jlDJjhQrwkazoNHWSFeW/z5uY19DGJ"
    "P4xwhSUtlkhDX7SKslK5t1uJM7KkUTMnCzSGYRiGSYy0E2cUHb0Zk0QZXJUaPZglCgrbKH9BQBxkSVEG9VFdheuq3U8cfOJMAquX"
    "DgkWHVNmmP3OoEN81xgXmeIMxBqxGSYu5n0UxslYXug+sKRhgIRPERo4IzorRXZ2dp1Ac61oCAtpBdhnGIZhGCY2aSXOdGFGzZi6"
    "tQzbvLyCqM2YkAAZmRAHrUVtzS5RUVmlwjWtXo4I8SY9GeLMhqlL7IMEDHFm8WPeHdHVvVj1j3EyhBd57Nybpt+IZUWrra0R5WUl"
    "HgsaiTQWaAzDMAwTH2kjzigapjCj/mU4Lihsqyr9ICAC1FxlUgOUlVepcAhbk6QJptTw+EFAxiWmvEjaiM0YzZoO3pOmOAM+/WOc"
    "sAXri4t0FCx0mRrVGWPAAJo5y0tLVFphRSOBBscCjWEYhmHCYyiCxsEUZrq1DM2YGEnYtm37qMIMfcuysjKUiCgprfCJoYSwhJGY"
    "uAgRFzPYEJeESWICwXr8QABmZWVKweWIrCBaS3GZV1Co4oRnRpZOOHquICnPhWEYhmGaMY1uObMJM1jJSJjBrKOmyQgQBjif5U6P"
    "UVEuRYG8HqBjurlkUbC0cEjVdBq2qJvnEhmxqcIwousPV17j7hNmdMxrbMALrGjOygnRrWgVatLaGl8/NFjP2ILGMAzDMNFpVMtZ"
    "NGFWWVmpxBIsZkEVOSp6WHRAaUl5RJiFxReuIboSxgg3WcGa2MJNlebBrRA28lvleZQb5ebly7+tPBY0PFd6zqCRfxMwDMMwTNrS"
    "aOIsljDDdAxt2rRTfmygGTMbzZg1taK4pMxnHUqk8rddAUtZ3IS4t2kpM0dvWgmRJPPWyRZBCA/9+pD30axf+QVtRGZWDgs0hmEY"
    "homTRhFnyRBmmZmtRXlFlSgrq1DnTJlgNmmCmE1pIcSCPVx3hwgl6GLfyx9K7GsSIV6NRAINffzMEa462dk5LNAYhmEYJk4aXJyZ"
    "wgyVdVhhBhmQnZWpJpUtlaLMnLssXsIIg90JCCJzhQBg6rVwosR7ke2KUDowBSD+GVKY5eB5SKEWBARaRmaWT6DhehZoDMMwDOOn"
    "QcUZVcKolLGPShqVNSptVN4xhVl2ppqqobS0QobhrdCTVb2b1rXkyQYj3BABJyQMLZekUr8huyCYYUkLIicnT/7190FDGaAywQKN"
    "YRiGYRwaxXJmE2YQW7GEGepvTJOBpZxMyAqjE7MZ06CkslQc/M9rxA3T/uqekVhEQ7zhOnjDqaysEi+98Z6Y8eHn7hmJGWwIvRJW"
    "01z33DfiwHs+FcVlNUkUnASWcIou0NAHTbRqHRFncFiWi4Q6wzAMwzAODSbOSJShMlZrZboVNCpr9ONq176969MLCTOIt+IAYRaE"
    "qXWi9UODMBv76k1icdEG8fCKz7wCzcDUZrYZ9P19seqOIczenP6h2Fa0QyxbubpOoIXQKInowt9IYfb3RWvF11uKxZiHP1cCLfns"
    "FpkxmjixSD3yKiLQIM5cgQZYpDEMwzBMA4kzqnSVMJOOFjFHJY3pL9q1w3QZ/qhAh2RmZsjrMeN/pdzWWccseihhIsJsx4/uGeER"
    "aKYeSkRDkIDThRlBAq2istI9Ex5bVHQBd93zjjAjIgKtPPkCDTOq4XlFE2iYqBaTCpNAw0LrVC4ACzSGYRimpZNycaYLM+xTcyaJ"
    "M2ceM7swQ1MZhMbOknKfILJNPWFOexGmmi+1CDOCBJq/H1qIkC0iwybMCAi0N6bOjC3QwiTKxRFm69yjOiDQRj+UGoEGg2GWmnTW"
    "XrTUSgL5hfLZO89fCTRZJlA2WKAxDMMwTANazkiYkThDP7O8/ILAJZlImJWUwmKWWGVNlb2OLrS+27RSHPvKjVZhRkCgXT/1HvfI"
    "wRYdQ7/5TkQTZgQ+e9MQaGawYYThzrIaceC9s63CjDAFWjL1UKtWu51RtUECrXVrkZubr8oAiTMSaCzMGIZhmJZOSsUZVbaq2cqt"
    "gFVTpnQZUpTl5mIUnx80jUGVFJfU9TGz9RerDxBmI9+4NaowIxwL2r3uUQCmdU1rd4Uw+/e70YUZsdUQaGFSrd+6RIqtMQ/PVeIr"
    "Fqm0oCHmeI5BgycysaxTVrZHoHH/M4ZhGIZJoTijypXEmd7PDEKrsLCN+tykdUZrZXEpK6v0dP63Vda0TiMRth8aCTNR40xgG4aY"
    "Ai1ATMQjzAhToIVFCbNHwgkzItVNnCS0bcB6hmyLNG/KckLlBbBAYxiGYVoiDWI5o6ZMpxKuVcLM2s+sVSuRlZEhysulMJP+4sXW"
    "D8203CQizAhdoPn6oVmERCLCjIgItIrYAg23TkSYERGBloJRnGolATRdBwg0DBCgssHNmwzDMAyTInFGlSssIFThUgWck5srMjOz"
    "XJ91QOugn1JVdY0UJJj3zCK03G086Nes2LRCHDBlckLCjCCBVlJZ4p5xMLVEfYQZQQINYemYLYUQVYkKMwLXjnlobgoE2m4pzlyB"
    "ZgEDBHJy81XZIIHGzZsMwzBMSybp4owqU5s4g1TKzy9Qn5tgAAD8Y1mmIExrWzzTaUCYjXzjtnoJMwIC7ZiXb/QJNCIZwoyAQHtj"
    "6gdegaalu0SKqWMerZ8wIxZu2akE2tLV9nQlCsoCBFrQJLVZWdkiIyPLtazy9BoMwzBMy6ZBLGfKaiZdm7b2FQBUvyQJZv+XF6r9"
    "MISdTiMeYdY2zz4Zrgkmqz3WItA2b90eWphlZWeJbOlisXW7RaBJ4hFmGdmZysUCAm34E3NSItAyogwQyM7NleVltyorcCg7VI4Y"
    "hmEYpiWRVHFGFamyemgWM1hE8vLyREaGI8J0UFljAEB5WYXyrxNUkUfFuGb5j9+FFmZD2u0hlpz7V/HC0Ze4Z6KDkZ66QNuyrUi8"
    "9Z9ZoYXZqSccLU6TLl6BJiVL3MJswS8PEgsuOTiUQKutqkmJQIsMELCA5s3snNyIOENZ4OZNhmEYpiXSSlZ6San1PMJMOhJlFRVS"
    "dMnj9u07qs91IKOypFioqdkliotLfWIMozHNKTRMvQZLmZ6EDO2aFZtWigPfDC/M3jvzz6Iwx2l2nfbNDHH2zCfUfixw7atjbxQz"
    "Ppwnqquq3bPBkDDr0gkT8LYSm7dsF//+z4eiKsS1nTq0E2OPOUqMe2phXMJswN6FKvOWrSkRI6TwggCLBa5dKAXdwJ7y2qTRSpYL"
    "LN3kt3qCstJitbh9Tk6OyMJ0G2pCW8filpBYZxiGYZgmRlLFGRyEGaweEGaVlZXKFRa2lYIk2/VZR1ZmhqqItxeVqGsTEWdKjLnW"
    "FeD0S9tdL2EGMKXHFz8sFEdjAtoYYWS3bi9ubTNWZAm7VUgHVrKfuMKMQJo2bykKJdAqaluJR7d0EWtLYgs5jzCTIH+Rm40t0PBI"
    "MfDDtiYpniUEWk5OtsyrbCXQIM7I6trYAu3bRYvEww8/5B45PPDwI+4ewzAMw9SfpDRrkr7TxRk1TWGyUZswgyiDACorq4hcb1a8"
    "aL6LF/RDq68wA4jS/j33E19MnCxEZq571g+E2S2Fx4YSZhAaZDEz6dK5vfosWhMnhNlDmzsnJMx0cG7jDUeLYZ3tc83ppKKJE82b"
    "gaM3pdhGmYk0bcryROWKYRiGYVoCSetzhgpUF2eOQKsV+fl2iwv6HtVg2ozKYKGhz7JPxLKbrNicoDAzLTKuYNynW99AgUbCLKdV"
    "7D5jHdu3E+edPk50tggzIppAI2G2oTSctevLAGFGtMnPFB9ceVCjCDTkbEZGq8DRm+h7RoMDdIEGaMswDMMwzZV6izO90kQlCodK"
    "FS47JyfSHKWDAQDoAF5SWu6ecQjTYmVOp4H+bMSCtV+LUW/+KSGLmXlrXQLYBFq8wuzUE49WTXU2baGnCQLttBNGewTa5sosccua"
    "DvEJs70KLXrTe3MItJlXNZJAk3FRZcPyzFE2srJzXIFfJ9DgmPRhy+bN4vprJylXVlrqnm1cEA+KE+LHMAzTFEmK5QwVLYmziNVM"
    "uvz8fNdHHRAMsJqVlUsBZQgVUzzEAzrwH/P2n0MJs0HtulubMj0YcYFAW3DGrUqgJSrMwtK5c7uIQIMwu3tDW5mnsfNGF2YgTHa2"
    "yWs8gYam7czWAdYziDO3PKFcURkD9SknTPIoLSlRS4zBlZWVuWcbF8SD4oT4MQzDNEUyJkvc/YTRhRkGAsBlZ2Wr5ikTCDNUysUl"
    "5Uqo6fUs9s1+Z62Mytv53Fs5T5fC7LxZT7pH0YEwm3HG7aJtniFGjPsCMy4dCzuKE9sNEP02tQklzIpbVYgzxo0WbQq8zYvmrSy3"
    "FgUF+aKmdTtx2eclYlfAyEadw9vuFs9PHCyG9evsnrGHa57EUU5Wa3HO/t1lPm4Rm8q8c6mZ7JZxeWzhBnHmPl1F53bhBWcQ6GNW"
    "GzibcCtRU1Ot/JBTZ2UazGfTUGzZtEnMnTvXPXIYd9LJ7l768OmHH4rXXnlJfPbJx+LQw49wz/p5+bl/iY9mzhT7Dh1m7RsaBMKf"
    "8d93xYknjBN9+/QR78n93TW1Yu/evV0fXnCf996dLlZ//70Yut9w8YPcPv3EYyp+e+7ZQ7Tv0MH1mTiI07R33hJHHXGU2H//A1T8"
    "guJ03113qntHi3M8UH7nyh8V3Xv0SEn6kgGsiY899GDkOaQD9Cwonygv44kjleM+ffuJ/IIoP7pTDOL+r2efESNHjbJ+n+h70H/A"
    "QLFg3jyVTrN8JCM/wgJL8z8efUR889VXYsTIkaHfByjff73r/4m+/fqlTdlubtTLckbWDF2cRaxmli8I6lNa1Dys9cOsgs2mrWmL"
    "4hdmhbmWvli2+BgCYMvWIvmFWimyRey5wrbs2iFuLZoqTnzzZt9EtaawsOXF0rXF4tjXl4pdIdYYHdu+VkzoUiS+mP+5mpaDCJnF"
    "isayoKkygRECFmA9w2hdsp6RBQ2ELT8tlS1bNovvV/2gXDQ++fRTseTbb9WLPx7mzJmtwsZ9tm7bqvZxLoj169cpP9iCclkpUPyw"
    "nwwoTogPpT8oTnRv+EsGdO/PZn+qjlORvmSwQP6wQJzmz5/vnml8zHyiZ0dlJQxUjtesWuWeaXjeev018dLLL4kfN24Uzz75D/es"
    "F+Q70obnQGVm4RfeZ5GM/AgLvvfIty++/FIJ9zDvAwizhx74myjasUNt06VLQ3Oj3s2aJMzgqK9Zbk6urHT9QWdmZKhO/uXuYt71"
    "rV8hzM7/KJwwQx+zQGEWAggzTDALq2AsIMzuLJ4h96rVSgLRlnoCZj4sW1sqRj45T4mgWECYndBpp9rHNBxvTP/AI9BMTBmk35oE"
    "2vDObd0zwSRToMGaGmQJy86um5iWxBkLs+Txk5NPUW7Q0KHumXCMG3+yOO7YY8XwA0aKQw4/Qu1PPPMs99PGAfdHPBAfxKsh40T3"
    "Hn/KT9wz6clhRx+t4nn2Oee6Z5oHF110sUrXwCFD3DMNyzNPPC5mvP++2m/frl1gOUC+I554DqPHHKv2jztxnPtpw4PvPb0DOnfp"
    "EvN9ACseBBm6DYDTTpvQqJbK5kzC4ky3YJgCzW41c6fOKHceKjDnMAM+q5LZMc0lHmF2Ro9hYgb6mGnCLFT17nqCMHv7vx/FLcwI"
    "CLQ9nrxcfLdphXsm+O5KmD0VTpj9au86YUaEEWjRgED74KpRDSrQ8MiDVg5Qfc9ciyzcbrecARZp9ee48eOVixf1Uj/9DNGrTx/l"
    "aL8x0ePR0HFq6PslCt7NiOf+o0a5Z5oHSA/S1RhCAcIMliewR7du4oY//DGwHOjxbMw46+jvgGjvAwgzWAYhzHJzcsSVV16lRCaT"
    "GpLSrInKUjVnSmGGUXY2qxmaM1GxVhjrQ8bCNp3G9G/eDy3MLu9zsHji1N/7LGa2it1nvZF+1q3fVC9hFqGmQox47RYl0Fxt4SMe"
    "YXZtzxrRO9srzIhoAi2MnFHTbMQh0IY+9Il4c/YG90xioGkTfRFt0MhNVc5YmCUFNGHgZYumGLgZ06ap5opokF8aBYlttHMNQbT7"
    "0zlMHEznwoJrkCd03Zdz50bCs0F5iW28oFkI4ev3SiWUH2HiirjFW04A8oquC3tNMomWxmifmc8iWh7B7yMP/C0izEC/fv3EjHen"
    "q+uilRdA+YP4NCSUNlv8gj5DXCHMiD5SfC5b+q3yG/bZUr7DNXSamyIJiTOqGFFZQnDplo2gEZoQZ2ph8xiY+sjk4+9mi/Nm2dvz"
    "TUZ36Sf+Mu5a9yh+Nm8tElNnfFx/YUa4As3WxPnj9qrQwuyyPSpFj6zoSzeRQNtZbPQHCClqSKB1bRM8Aa/OmW9+JeYvTcxaByDM"
    "bNOuAAwsofKFMqfKHYuzhEGn39tuuVm9bNEUA/fWO2+Le+++S3VGDupDQn63bNyojrGNdq4hiHZ/OodKhM7FApUS8gCrQCBP6Lqn"
    "n35K3PXnO5TQsIH+Q/AX1MctCFRSd97+JxW+fq8/3zo5ZYKG8iNWXFGJ3vC731rLCaxFgeVE5hHyiq6ja1DuGopoaQz6DPltPguk"
    "IehZ3H/P3ap/lg76bNF1+I5FyycqM4hPQ0Jpo++Hju0zU5gBpJv84tnefOMNgeUV55GH+E7RNdhPZRlvDtS7WROWDFSWsJrB8pSZ"
    "6R/FqCpd6b3KIjxMa0msSnf/vYepjv1hmLl5hWr+BPp8aGHp3LGd6N9nb/comKrMmtjCzOWlI34uCnP8/d66d8wVl/Xv6h4Fc2GX"
    "ctG/INy0BX322lO0bRO/yZwewfsLN4tNxbEFNfjV0L3EyIGJj9rBc4f1zNb3DPOetc7ItIqzlijSICDoF2i84EWLCoRA/xg0xRDo"
    "ePzKC8+7R40LpTGWBSKZ/OvpJ1UeEH1691J5BNCcA6GRrF/9SNdTT/5DdawGuA+aiwA6lT/5+GOBFXt9ykAYYBFCJUqY5QTWorff"
    "mOIe1aGsTjKPqE+Sfg3KXTIEGllgUJaTBfKZOrkDPAf9Wdg6vu+5557ungPSivJC1wHkE0bHppJU5IdOx06d3D0HlAWkU3+2NDjA"
    "/K4iz1COkYcgTL4yDvUSZ1RJklUjJzfP/dQLrGaVlVXWPmYmtvUWsbg5USCFzXtn3B5aoJ076x8RgWZiEwImY44cFVWgQZjdtPXf"
    "ci+EMBt9qTh5v+PdI5Pd4p6zB4sr9/V+4XUgzIa2DSeW9hu0jxg75hD3KH7QTAlrWBggzO47f1/3KHHwPIJGbkL0UzlDmSPXEtGt"
    "Q/FC1gK8IG++9TZx21/uFDfdMlncefc96oUL9GaaxoTSaPuFnypImB2w//4qT669/gaVR+hfQ5XKwgXJyZ9XX3whImLQoR33ueu+"
    "+1UncYAKD01kNupTBqKByhXCjCxCqID1coJ9qpQhtszK+EVX2KMCv+531/vKFq6pr7UkrOUvHvCDhJ7Fz876mXoOcOgcD/CZKUZ/"
    "6nbuRzqxvi7SivKC63CO8gllKpXNeKnIDx0aNIAyimeJsoB00rPFdwUgj9558w21T6D8kuBFGLZ8TZcfg+lG3OKMKkSqHMmSgUoz"
    "N9ffBAbLGP6VljmiIowgikVeVr747+l/SopA07FV9ohvkECrjzAz84FEaZBAi0eYHXP4geKow0eq/UT0yz8/WNPgwsxht2gd1LTp"
    "TqtBZY0HBtSPkSNHqtFZBDolH3zwoe5Ry0SvQA859DBPR21UUN2776H2kzWlwfeuSDn8sMM8HfTRSZzEzIoV36ltQwDRhOZIvakO"
    "1g1dHKPMXCqFKqF/hutJ4EyYeHqkUzzy8bKrrlb7YPmSJe5e+rBy5Uq1hdDQO7mjc/zgQYPU/jfffKO2BNKFZ2Xr/I9zk377O/fI"
    "EVBNGeQDyqg5eAHHF15yaUSIbt++TW0JKr/IQ32gAfZJ1K1fv15tGS/17nNGlSWWagqaPqOqujoy0ahpGHHr17gpyClQAm10l77u"
    "meg4Au099yh+TIG2Pbu4nhazYEFhCrR4hdmQQf3cIzumPNZj8pvnvhG//M9i9yg6yRVmDtEGBmToTZtuGWRhlhgrVtDI4TqSNedX"
    "U0WfPmDt6tXuXh3btxepbW5AC0E8wOJEQmb4CKeS0unXbx+11ZtYU820t9+KxElvnnvh+efUltBFvS469PncdLEJUIlTBV5Wnh6r"
    "SeiQdcf2LHr06KG25CcsepqbO0Pd745ZXumY8lBnwICBaktNnoyXhMUZKkhsUVnCZWXVtbMTsA61khVtZUXdCE2zLrVNleHrhxYg"
    "ZCDQXj/jDjUiMwznfPgPMfXrOoEWpplV9wKB1rtnd7Gu1RZxx+ap8kwsYZYVEWamwTDWrSHQ7jmiX/zCbHB0YRYNCLO/L1rrHkUn"
    "FcLMwV1z04I+rQaVPxZn8TFs6H5qixei2dQyb948tSVLQUuEKtNZH81SWwJ5RZVz/336q219aMim2rCQxQyWPDRbYQ4rgHQno19Q"
    "Xl64wUWNSV5e/YW3TkOmmX48NBXMvmyMl7jEGVWEVClGLGfSBTVpQleVV8a2LkXDNp0GOokTd5w4KbRAgwVNF2gmvmZXrfIvqSgR"
    "N69+UdxXFLuJFOtv3tvxDLFPrvsiN8INoykG5m0OLcxe21gonvyiwhquL0nuVic9hJmDKjdGnAEsZ4g7lTs0beplkokNmmzIIjLl"
    "9dcilS46FEesB8NHqG1LZPToMWqLvKDO9sgj5BVA3jX3uZ3IeqRXnvGuIME0HHv3dJrAUWbNPoBM0yVuyxlVghFhpqxm9jW4Mlo7"
    "AwF0bKMmTfGQCMkUaDpU5UOYHffKTWLxjh/dM8FAmP2l/Tixu3a3mDl7vvh2mXyxhRAPerPwjA8/F0tXhmvSgDD7rCRLPLRonfjt"
    "C95+EcB3a+PEdWkkzAC0GcqODQg0KnvctBk/aGo5fqzTxA7rGTrjYuoD6liO5qxkiw+IG/pV36FDR7VtSNatc/qIkSgFZCGjzwik"
    "nT5THe5l3mApHmp6sc2IrqcP6yGGQW9Cber9kWzYRMKGDf53pz41SZ6Rr6kiWj8+Wn6rsUgkP/S1YR9/+KG0Emj0nSsvL1dbHSr3"
    "+veSqaOVrNhC12zwSoIMU2dUVlaKiooKkZOTJ/KM+c1ggcrOzhQ7dpapObcICDHTOoV+RvooTZ/1CviuaS0rZ6/Qg4+b3r1fPPr9"
    "HOdEDP7f8FPE5Uec5x454N5mlpRWlSYkzHTGHDZSDOzv7ThqJhMLe++WaYIwW7bS3+fFBgkznauG9hC3ThgoCvOcNUBt2Ukn002Y"
    "ETUy/6qr/VOv1NbWiIryUmWpzZFf6szMTNUMiudmLTdJBs1bmKNHByO1GhI9DkH3htVHF1yoGDt27CjzzPkhFdSXCcKEmmKCriE/"
    "5eUVEdFiO0f3pX5MACPhIID0NGAkpC5WiGuuvEJtgz4H5CcoTkVFRZH7owMyOi8DTOlAU4pkZWWKvNw80amTIxz1MEyoo35VVZUo"
    "Li5R1+h5iRFt6G8VJn2YT42uxejGDh3aq30AsUeWTNsztpUBdMif8urLal8Hcd26dVtkQAOFjUoR8afPwjxfQo93lvwOVsp7YI5L"
    "8q/nNYDowBQbgK7ZWVIc+fGOcxgFCKjsIq/RvGoS63NAfsw06uURIy3RoR/oI1SjPQvbdykadD89n6icmZ8lmh9Az19gpkFHf87l"
    "5WXKuNKmjTO9U7TPomHLIz2/8Rwm335H5IcNftBM/sPv1WfR0tWSyZgscfdDAXGG5iQsbg6Bhi9+m7ZtfRUjps/AudLSCl8zmukX"
    "U2WYEtHnB8LF3QfO596LcObYfQ4RO7auFfOKYo+omrFxmdi5ba04bp/gUWollaVi7Kv1E2Zg1ZoNojA/T3TuVDcXmN84tLvewgzM"
    "3VQspi/eIs4Z0V1kZ+E5uB/oyJPpKswAni8NItFBOaiqrFCCDA5lp5U8B/9mmUkFWzZtEnONGdzHnXSyu9cw6HEIuvfSJYvFSrcp"
    "qqhoh/q+FpeUqH24IErkS5P8BF1DfrAlbOcoDAIV9ikTT1f7ehpGjTpIdO7qn+Nv+lT060Rn42Giu6VDMV7wM977r9oPihPdH5XN"
    "Ly67XGRlOxVq3377iBXLl6pr8E5DpYl9MwwT8gNhRtcQ6Kt13DhnncQw6es/YKBY+OUXqoKCo7DhcEzYnrEe/tGjx6h0/bhunXjv"
    "vfc84cAhrsgHOqaw1fPVPiOC8pKu1/0irLLycpUXuv8NP/4ovv1mkdgst7M/+VjMnFU3Bxddgx/5ABX3ZVLAtu/gvBup7HZo314c"
    "evgR6pxOpGzL18OY445zz3ohP2YasQXoV3meFNJEn779Qj0LCkP/XkRzdD89n4I+SzQ/QN/+/UVWq9bihx9+UOGaadAdgecFMYh7"
    "h/ksmrPlEW0Bth/LMlBeWqLS889nnolcc84551m/Hy2d0JYz8kZWM4gyWM6w376Dv2MfrGY1NfIB7fC/6NRSTtptTcsZ8IkzWRHj"
    "Japj1sXKmub6iceCdkXfg8Wd437jHtWRLGGmM6BPT3HMUQepffStonzAF+HN6R+KbbJAhyFImOkM69xGfHDFKGVBM/PquucXxy3M"
    "EET01CUPPP/KqhpZ3vzN4OVlJSrvYDnLlpUSCTWQaoGWbpYzstSY0Hp/eNEfccQRYsV334k9pcCJp8NzIteYUBhYjFyfcgBNL5+6"
    "FfZhRx3tGQFIXH/tJPUCh+g567zz3bN1YMJTzOYO4CconuiTY8sjgLxEUxaaXWwjyoKA/23btqlr8vPyRf/Bg+NOH4DAXLp4sViz"
    "2rFYEBicAUtEkFUBVjLMzA6oDOj3BBQGLDx77tFd9NvHGQGqg3Ssl6LO9llYkA96/i2SeWqzPFJZBHQN+jeOOPBAT1MxngmavDp3"
    "7mJtYtdnrMe8a7a8xezziAMsSPvuu68njQMGDrJaMmM9i/p8l4CZTzr1yQ8dlIE1q1b50hAEmvWRDlgCTaJ9FgvkEeU30hY0d6Ju"
    "vWS8xCXO4HRxhiZN9AEqKGzj+nJA9ZidkyVKisusgwGyMlv7rCJmleoIF/dAAouJOboymjgD9RFo8Qgz8Mg+F4rSzeE675NAk9FV"
    "aYxXmHXsMUBcPCtcvwISaFiOibjueVjMws3V1NAWM52gps2qqkpRW1OlmjazsrKUQ/loCOtZOogzoDfnYd4pvYLSmzjM5qWmhN7U"
    "RM2hBMQJZheHeNObgNIJPIfl3y1XFW6sSlVHFx9BwhSQeIVouP6m33vKgB5GY5QBNMWhbxeayVBGMZs+Jm01++slAgQIlkYCtvJP"
    "zYAAk50GLeQdBnzfsYoD8rkpf5caG+Tj9GnvqGZOgCbPceNPDuyuwMQpziB8zP5m+QWFaooDHQirbFlhbt22w9o0lZlhEVruloB1"
    "zWNNs1S6scQZSESglUphdlxYYZaZK1484ufiJ8OPV02Sy78P1yQJgXbs0QfFLcwwXcbgQX3Fvz/bIH72VrhZp5VAu1IKtLzMuITZ"
    "q6ftJ047NNxEv6kAj7/SIu5RBsvLiiP9ziDOGqrfWbqIM7OPCSwsQO/7Yau0mxK6AAPUj8bsE2YKt3SAxBGeCyb3DYof/Okzu+tp"
    "w/PT++mY6AIMBJWBq675tXWi1KYMWYaJWOWfxMHEM89Sn2FON0w0rFtUzWcBqA9WU8xHPc3N7fm3BOLqcwbh4+tv1sZZd04HE89C"
    "bZWWOS9V1adM7TnY6k/zlGk5UxgXQozpc6DJqln+9V50XP9DxY4ta0L1QZu3fZ3YsXWN+NO8KaGF2ZenTxYH9z1Q3btPzz3Fzp2l"
    "oYTWVuln544S8cXXS+MTZgP7qswatFcbMawgX7y2dJP7aTCbyqrE9G+2iKXf7wwtzF6RwmxCIwozAKFla9aElayyslwNBsA+ykFD"
    "9TtLhz5nAH1Mdm7fLtasWaOOzb4fEDLot4Lml6YK+tzsvddeYvmyZSpdcEgj9W1ChXnGGWemnTADX86fp2Y+v/lPt3tG05nAH0QG"
    "PT9KGz2/LlH64iDcavkDGfehPj62MtAcK+YRI0fGVf7/9cxTSmj9uH6tqJJ+Ppff4R1F2zx9uMxnAQdQzi7+xS/FPgOdSVObCpTm"
    "grxcMXDIEPcs01QIZTkjL2Q1q66uVlYzvBDat/e3R+fkZMkvQLXYUezMBI0+ZboFDfWnWYlKLx4x5rOcAeMaZSmzjNjUcfzsFjdO"
    "vy+0BS0UrjDr19WZ9FVFzY3u/z6aG9qCFobs7CxxxKjhjjADWiLjsaCFBcLstEO6m9nd4KCMBPU7KystVmWEmjYbqt9ZuljOCOpn"
    "hH4dWDoFUznsvXfPtBQs9QFWDaxggKYypLFTx04qjcloJksF+kjMoH5jwLTWYKqRvXrsFVfa1MCId6c3+zJgwyz/WFnB1seQrEho"
    "SsMUFRjVOnrMsVEtZ4k8i3QCfTJnfvA+W86aKKHFGRwsZxBmJM52S5XQtq3XcoZq0exvZoozAMuYTphBATjWfcQjzkDSBJoUZgvO"
    "uFX0NZaO0u/99TfLxKfzv3aPEgfC7LQTRosuXepGeSJb9HxIpkAjYUakUOfEBM+7ugZlzt/vDNNpYNoRiDMMCqApNUBLEmdMeoIm"
    "WVrOCGKAK0eGYeIhrkloSaTBggahhgrRh6wY8Y+G0AJXG9Ubs9I1+63F4i/jrg09UW0gUph9MREWs+hreg7bd4Ca26w+QJidesLR"
    "HmHm4M2HU6WYeuknw9yjxDGFWWODshakszIzs9XnqqldbskxTDoAMYbOznCpFmbKcjZtmvrhALAPqwnDME2X0OLMrACDxJmyiMn/"
    "sHgQNhGFfmg6idSrtsoYfZB0TB8QaM8f9Uv3KE5cYbZPt77We5sMGtBHjD40MYEWEWad/RMJyqfg7tUBgTb9rP1FRrZFMIcg3YQZ"
    "ocqJRaC1znSmVtHLJMO0RNAch8EhGFUIgYZ9mmKEYZimSVyWMygoVISoFOHMUZoAlamtGcrEtIjYBFyQ1SQeEE8TLEQet0DThFkQ"
    "pmUPeZWIQPMJMzMfArTI6OFdxBe/PChugQZhBnGXjhIHeYp/JlhblYSZ7himpbFXz56q03qfPn1E527dVGd4Gr3IMEzTJGafM/oY"
    "TZlwNPksRsV06uQfop8jhQWWa6LBAEEkNJ0GMASQGkjg7gPVx8wQZKZoon5oWF8T62zGJNL53xRmZlzqJpUl6N5YXxPrbMYiS/Ux"
    "81rM9DU3I3hvre5Dt162tkQc8I/PRW1VbJFMwowwgjWzu1HAoABfOZCUluwUWHpHTUaLuc7cQQHm804m3OeMYRiGSTUJ9TmD+MnK"
    "DJidXtaLen8zwt+M6a9sE8EULpY6PJCTho2NbUGTwmz+hFt8nf9BPBIgjAUNwgwWs65d4p+RWWfAXoWhLGivnOoVZumIspwFiC1M"
    "n0FlUn/sySpbDMMwDNMYhBJnVNnplZ7ZtwtQHVpV7RdnZv1qb8Y0BZy7EwcYwWfiE4buFkQVaK4w2wcWsxDxtaVJBwItaJAACbMu"
    "nSx9zCxpMrLTmygJBNqXUQSaI8ychZDTGpmntrIG8FzxQ4EEGsMwDMM0B+KynAGqDGnaAi+23kF2bHWpT8BZ+ouFDd+DKaKMcCHQ"
    "Xjz6EvfIRRdmAXjtNXbMNNksaH5hFr/QsMUlSKBFE2ZmfBtb80S7fesMJ126OGORxjAMwzR1QoszqgDhlLgxa3GJOiX/2AYEJKvO"
    "NK1VtTYBl4DCgEB7gQRakDCzpDleEBVdoGECVdXHTLOYhcmrMNmJ6JoCLZbFLFnPKZkENWvqgwIYhmEYprkQakAAHAYDYPJZWlOz"
    "sE1bkWn0O1NramZniU2bi9wz0TEHBUTrUE+gics3kMCou81BAU6/tBjhuveetfwzsWe7rlaLWWsZX392ecMxZYR1GSqX71etlflY"
    "ILp16WhJt7vjgv5VniSYN1KYaaoTWxgkUFxeIw4c4G02RT5ETxH8uDuNBPoRVlZVm49Q1KjJkEsbdI1NHhDAMAzDpJpQljMIB3L6"
    "sQmE0+54euQbhOqH5pMSsQnTD404qv8hgU2Zluj5MONrG2VI9Om9l+jSCRPMhgjY9GK5xEyRHl9Y0Eb29/dnS4TUyJ5gnPv574q5"
    "zhiGYRimuRF3n7MgYUYkIp6iYWoom/hLhliwdub3CbjkpK0VTFoaYURfKMy8crfJJlXhBmPvy0jNmoDKZbSy2ZzBLPGw6pHDMcMw"
    "DNM0CdWsiSbC2poaUeU2a5aXl4tOnbu6PurIysxQwmPL1p3uGS/mGps4Nm9uVsLJWgDdtGjpa24Stms82SOPTb3m+HEPJHpTImHe"
    "G3lkikwzXGWF1NIUaq4z+c+4tS9NqnXU58mIn7slzLg1PFgAvdpqhSzeud3XrIm8M/M8WaRbsybigwWdaZFtHUxEioWesYSQCcTb"
    "Yw89aF2c++Xn/iU++fRTtQ+QvmuuvCKyn4689fprYsb774vjjj1W/OT0M9yz9YcWML/yyqus+ZgolJ+xaO5N5qnK33jRF6q3ge/H"
    "sKH7iePGj3fPJB+sx/r8P58VP27cqI6TXZYTgd530RbvbyrY0pIu5c9G3JazZGKzVvmmvbD4SQQzXKulLBaWa0ybjkU/+Eng3qGm"
    "0whBkpKdNiSrfDRFsGwPXja6wDpg//3VFuA8Poc/E5yj6zCj/J579lD7WJORhJmadd4Ni2HqAypBCFJUkE0RfFewLBbSkSqmvf1W"
    "RJjt0a2b6NzZP8k703JIqjiL11phrVeNIGzWEvM+iVTPtko9kXDDNOOa2RJOT8SfqmQ3KacXwWULz1I9z3AZ2yyAiHrp5ZfU/uBB"
    "g8Sdd9+jfg1eeMmlaotjnAfwZ1aKy79brraoBG74wx/FWeedr47XrHYEG85fdc2vI78w8Ssejkku+MUO61iQa+4cfPChqlxh2al0"
    "AHExn8HNt96mfvQAiLRULSpfUVGutrjXTbdMFocdfbQ6bkzwXJAneE5MwxJKnIW1TsQSZ6GsSiEw72KdDy1OoWjFlu5khGvBJwxD"
    "5HmY7ExMGMYmNblgB2kIyvawZbO58caU19UWlq0rpIjKLyhQxwSOcZ4sXy88/5zaElQRTDz9DN+1YOjQoaJXnz7ukVDNK43dxMI0"
    "PyBAUK46d0lfKxHihh89+MEC6AdMqjjk0MPcvcYHacfzSQeh2NII1ecM02jswrqaMfqcYV1NLN20vajEPRObrMzWnn5oqZpOA5jh"
    "+MK13NukVYa105a7dTD7nUWbToNw/ERPk386DXiIHhcjCIUvXKTb3SfM68xrGhLED+tr1tb6RfhO9DnLyYmsr5mRmdns+5zhl/vT"
    "Tz+l9vGrPlrFtmXzZnHbLTer/YsuuliUl5WJOXNmiw0bflTr46LCycvLFf37DxDLly8T27cXiaIdO1RTZ4cO7dUvZryYqTnH7HeC"
    "vl7z5s1T1xCw2I0/5ScecQeQd1Okf2q6AfB75tnnhK6cZ0ybJmZ9NCtyPzz7kSOdOQPRHItf+bqIRPrfefMN8cWXX7pnHKvguPEn"
    "if1HjXLPBGPrk4L+eq+88LxYvHixykMinnCpz1k8fV3QFD1z5gee/IP4NvsVwh+eMZ5dXn6+EvLIL2Wh6twl8tmWLZvFxx9/HEkD"
    "4n/uzy9Q+1NefTnS7A1gzfnpOed6hDyep62/o+4X/RfXr1/nK28TzzxLlQ/6nI4JlPHp06Z60mrLX/TTQlyRHjwXs2wcccQRoX5U"
    "0HM2y48O9cVEnuN7QPmMuG/bsiWSz/ozDfP9iJVHAPd6993pnrQNGTLE90xs+Ybv8oEHHuhJV1AZNr+PlL/o9kDWdWC7PihOlL7L"
    "rrpaPPvkP8SSb791P3HKr55O/X4DBg6K5CkIep6IywyZN3pZtqWZ3t30/IDt+w2S8a6qL0nvcxY0RUUQpmix9QUzK9pkNd/5+re5"
    "26iE8uQNN9p0GnUkkCZrXrk7LYQWllyF3vQY60WBz+EP4DpUyHgZ0UsMLx8cb5GVC7b0IsTWOb9ZHWMfTueZJx5XnfDhF/fASw8v"
    "ULx8H3rgb+pFS6BywYsR9zP93vXnO5SIigVe8uj3g/vh5avCyM1VFaY+gIFAmAgbwgz3gn9chzhA3CJOiXD/PXerMJGHCJPSQuGG"
    "SUu8IK/RPI17RNIu74lnYvYrpGe8cOECFR96poA+e1MKVjw75J8e/ycff0w9O/jBeSo7SO/bb0xR+4AqOvij+Oh+UQkDVMrwY5a3"
    "clmhAvqcjgGeM+JtppXyV08rrsP1EC4oG5iDE/5xHe6JNCarGXLFihVq26/fPmpLefnZJx/78hmg4je/H8D8fsTKI3r2ejjwi3xG"
    "WSTwTMx8wxbXIR4QioStDAPE7YG/3qv2AeUv4khADN15+5881yNeepzgh6D04TzC1/MC51HmCLrf/PnzVVroeVL4SAd+oBG4D8LF"
    "eT0ulGbkXbzo7yq9/MXzrkoGGZMl7n4gsOgoCxpGbdbWipqaGpGf728KwchKCKmycqeQ2TDFg7IYufuEWeH6rCC4wDgHa4kucJyO"
    "+t6QzXCUpczdJ2LdWx2ZnowTvvhKfOEo85p7IIHOMi/zHftvjJMerPd2t4T/PvFf07C0EjW1zrJhJhXlZWqUZmZmpmekpi1NyWDL"
    "pk1irvGyH3fSye5ewzDtnbdEUdEOMXz4cDF0v+Hu2WDWr10j1qxZI/Nvl2qeQXy//WaRCgO/GM+/6GIxYuRIdb5avgxXykoDFoRJ"
    "v7teDJS/hMH0qVPVltKKF9h7M2ao/Z+d9TNxzgUXikMPP0IcfuSRYtFXC9XLsWjbVjHq4EPUy+yhvz8Y1W/xjiIVhyBQkb3s9rH7"
    "ycmniF9ccYUKY8xxx4mN69eLDT/+qD7r27dvJM4Yjbpl61Zlybnq15PEUWOOUf6zWrUWS5ctE999t1zFISs7W/m3gYoX+TRq1EGi"
    "c9euqqLHL3S8rG+6+RZx7PEnRNIy7/M5qoLoLiuHvXv3dkOwQ/mJUfCrV30vli5Z7HOUDlS6b739ltrX0457bpMCAWlHWvaX+QeL"
    "Ba7FM4TgRjzPOONMcd6FF4qhw0dEPkMLB57x5Vdfo8IaMHCgmP3pJyr+hYWF4vqbfq/SduTo0ZEyUV1VpY7Bqy+9qMJH3l57/f+p"
    "MPDZHl27iQULvlSfoazgvK28IS+Bmb/KYjHFEYGHH3aYuPo316kwxp54YuQ5L5JhjTroYJVW+j4i3uZzXiXFFOJRWVGuymE0KB56"
    "+dGBIJj/5Rdq/yB5bzxfykt8t/R87r7XXsr/nM8/V/5hsYY1Cek4evSYSJlfItOBeEbLI3r2CP/XMi9OOW2C8o/0L5TxQfnG80Gc"
    "6ZnAwnP97/+g/Onlfdu2beoYYX4w8wMV5u13/j+VX/A7ZMi+4sv580SJFDx9evVW96f87dC+vfIDnn/2GSmgVkXidKIsk3j2dD3S"
    "hnJJ32fKW+iGSy+7XEz46U9998N++w4dIvdD+YQo+u0NN6r4Ifyd27ervK6qqozEZbrMm6++/loJst/IckhlFvH/+quvxJq1a6Om"
    "xSx/eFc9KQUd7o931c9/8UvlN553VbIIZTkLW9GFmYDWtFaFsSqFub3pxZxaAySjurbF1p8/sdMUBt/0GZY0+QhxazO6sZpy0wN7"
    "HFMlwpoCeXl57l50wvqLB1hlACpEvT8KKkw0jeHFSv3aPp3lWDpsfi+VFRHAL27917YJXqIA4ZrTGej9gQiIOfwCRwViNrPgehU/"
    "WaEvmDfPPRsONAvj2uPHHu+xWiL87t27q32yNoYB6VbWAIsjPpvtWAVR6eppxz2RdrISLZAVj8nFsnJBnuvpB8gvvckHzUqUhyee"
    "OM6TNjQvAVgSiI4dO6p8GHPcWPeMg03YxAOlFWHrzWiA0gqoTBG25zzmGGcAC5XDMKAJ8r677vQ4NEHDKgeQR7b+Vxg8o+czmlcB"
    "BLDeDIvPJ/32d2ofFX0sq94H/3PKwWlSlOnNvng+55x7ntpHnEFQOlFmEA808+mgzGyWgoVA+LgP/AaB7yjKLEDZ0uOEfZwDtu8z"
    "miT1pkP4797dWUpQt5wS51/0C8/zPPaEE9UW32sCP5QA+s7qZRb3wf0Alakw4DtEQt98V9Fzi/WuShZJb9aMF1sTJaxpOvGKh63y"
    "18O3S5aIb7+tc8CsyG3rcsbEGhfvOZve9Ou3+NIEbFf4pEkIrZKIFktn/Ybnqp5tCxZqDc33UvwAW+dlvHTRp4P6daxY8Z3aoq8q"
    "mlZ0h0qWKtzVbpg2qFkFc03ZwAAGneXy+w/QbIf+KOZ9iWXLlrp74cALG+lChYdf2cqyIcND8wmaPeIFljBYSmyOWLlypdoGdRSn"
    "SvfrRV+pLQEhoVeGOmZ+AfRzAh07dVLbaEA4IR/wrCGEITKQD2juqg/bt29T26DRgZRWKlMEKnm9Ik8UCCZU/roDEH+osKmC1oFo"
    "1kUKQDjgsKP8Qg7xxDUg1uAC+p6hnOrlF27ZUqe84V4QC5RnKIfXXztJlUlYuFFOIcRJjPeUcUV6wL133yUeeeBvKjyUZZRv+Asq"
    "N/QdxfU2PzhHYZvfZxL5YUDZ1cUWMI9R7iCkAPLCzB9YCsH69evVNgz0HbK9q/AeCfOuShbOatgJULurVmS09i6fg/o73uoRlX6s"
    "OhXWNVNYwQKn90/Dr9V//fNp8ZH8xfLBBzPds14mTpwgfv7zi8Sogw4R+fl2a8KaNavFX++ta8evD6dNmKi+VIu/+UYehcuZnj33"
    "FgPkF/ewww4X3bp6B12sWrVK3Kv1MQjDIYceIgYMGGh92c147z0xxR31lwxOP/10Mfb4492j5OE0q7sHBi3RcobOsqg0zAoqCPJH"
    "c5klA3opxgMqjUQEjM5ePXu6e1727umdj62svExtUXHpVigTEgPxYA5KIFApxZsvSE9QRUjQfYIsoEHzYfXr18/dSz4QA+gQTlYU"
    "girmRCExFCQQUcFHe571BVYj3aIYhh49vN8r6ksGTEFB4Jow3wUqT2Y+m0AsQFjhuVDZxDV0HUTFhImnKysexCEsfZhXjb6TcMhX"
    "PD8MsDGtliZk8bKBz+g5Jgr9UIiGbm2LViZ0i29YKE+CWLt6dczvbX0JbzmTlSBZKOAwetNKDAuLPjKTqE8FC4X7wP33iP779BG3"
    "3XabEmY333yzeG/G++LT2XOUe+7558WYMaOlEHlDnHbaT8R55/5UzJ9nNyf3lC/5Sb/5rTj1tAnifx/8Tzz19NMRh+NoFO0o8vjf"
    "sGG9OP/nF4rLLr9StGvXVp57yuOKdmx3r8RLaaU6N/nWW8U5Z58tevfqKa668kolyIjevXuL6353vfySTRTv/+998eRTT0UcjnXo"
    "/CWXXCqOll/aQYP6i3/96xn1GQmd9RvWecIgR6z8fqXnPI7B9qLtnvPk4vmFEi/RBoFQmWwp7L23I1DwAoxlXsfn9KKk6xqLaFYi"
    "OPyij8W2rVvdPS9bAzrp4he47V7kMFIsHtSvaHdQAvpEoT8RwsGI3WgVVn2IJXiCmlFT0ZxNUIdyVPr0XDFy+K777nd9JAZZJoJA"
    "pZjudNF+VAd9P8mqExb0f9LLrenouwOL7m1/uVPVE7gG1j6UH5RXdLCnzuyw9GGqHcyHiDIMUYrvCsQgBtdgUEY0yssr3D0/GPHd"
    "0NjyRHfxEutdNSLEiOz6EnezZrSKEBaO1phqIk6MVkwRtrURVq6fn3eWEmVg4oQJYtnyleLX1/5WHDBylOpkOGjQYDF+/Cni9Slv"
    "KZEGIOCOO+4Ycd9f77bas3pJgTZ69DHijjv+4p5x+NWvrhb33f+g+NuDD4n7H/i74R4Szzz7vNi4aYu4dtIk9woh8vPyVTxul2FB"
    "IOo8+tg/xAMyLLi3354uVv2wRjz2+ONShDlWAIi1IUMGi/ffdzpegz7yS3XssWPFX+QXUOfqq68Rf5cVhOMeFeUVVWLmzA+VtRCs"
    "khU0hNo555wlysq8Lwzcb+rUqWqJJLiHH31MuXPOOdf14XCuPH70scfEyy+/Iqqrq5WbJq+j+KaKIFmGDqZ6WWwpIm3EgQdGKmx9"
    "BJ0N+hz+cV2ywIsc2MQSKgD006HpIshit3XbVvVr03SocNEsUVbmWLtsdOjQUW2DmiHXrlvr7jlQEwpGe9nuCXBPW1+XaJAVEi9v"
    "WBdgiaDwUgWJvoUL7NaTVFhGo4HmL1gjUKYwgTEEAfIAVqJYPxZiQf32gtJKz5nKQzoCyxR9P4P6NFJTdaxVAND3DmBKFL38kkMZ"
    "hsM9qfkNzwDiC5Y09NObfPsdEdGLbgTUFI8trkMZhrUQE99Sf7NvVGuPnzzpH+D5k9DTwTmy9KZ6YmGkn8C9zLzBOeRN0A86G2Hf"
    "VQ1BKCVFlR5VfNja+oEl2rHcvCxMPzT8Wpxw6kmRJkwIswceelR06txZHduASHvzTWfUE4CoM5sw9abSvu6QaaKwTRu1jZbMPCnG"
    "brjpDz7BgqbZPr37ukcOBfILp9NFxv28c88XU6e967n+lFNOqbOguffeZ5/+zo5L27ZO3ADpk4MPOVQ8/8LL4jfXXuuckMB6ePuf"
    "HDG7ZLHTL+e116aIsWMTa45EM+brr7/hHqUGld+2PE+wvDV18EJFh3SAX7n60HIdnKcpJuAf1yULajLDFAZmhYx5xQD1qxk+wpld"
    "HcPj9SYfoCqKd95WHXuDmoAAhQFrjRkGjs1mH7xIyWKgT70AEF9MyoumEFje44GsAp0s/V/q25QTBHVJsOUf0kb3pTxqSMwyhaZO"
    "IhGhNnz4CLVFuTXTin5t9JzTaaJWG5jvC9i+HxBGKJdhfjBRH0vMXWaGg+83yvAi+R0C2OLYLO94Ruh7qfZl/QSBAX+Yo86EugeQ"
    "fxOIPhJ6r774gtrq0Dlbn7FUQO8YeufoIC5IJ4w4YYn2rsIxvavyjbo7FSQ8IKCmutrdM5AVJhY0jwaJh/pww/XXKWsQ8cfJf5Ji"
    "x/uisNXdGMp8z911guzW224V8+Y5Q55DE0MUQKBdcMGFYs5nn7lnAjAygoLt3au3uPGm3zsHLk88Hv98LcTv/+BMQkr89b77xGb5"
    "C2eHfEHAmjds2LBA61QY9ttvmLLQzZ492z2TXKKJfn3qDPrx0BKAtQJNFgAvjJtvvCHyyxlOHbsjzOAP/pPJKRMmRsQPOoHTfTG6"
    "jSpQGi0HoUSjIzG/k5qvTPrF9il3PiwaWRUEft2TFQGdmPUwcGwDI88A5ohC52iKI+KLeKMC0UfShYEsOy9KEULhIWw9Dhg9B9GZ"
    "LGABoSYnPf9wX1rCC88Y+dwQkEUE8cHzpnzQnz2guc50IIrhz6z4CEorMNOKZjmACrmh0pooGDlK34/Jf/h9JB1IOwQDCPODifID"
    "lir9e6bKs/v9xsS8gAZ54Lxe3nFP6neF5jg4xA2iXn9vII4o18A2YISgUaLok6Vfj33qp4XRkw0BJvNFWlDuzLKIuOAzGuUZBpQr"
    "lC/buwrHAO+qZP7QDSK0OKPKD5Vh0AzsquO23LbO8A4UMDGn04h31ORHs2aKKW/UKWX0MbP1p7FOpyHvffa5zizYxC9/cVHUJhUT"
    "m1Qw03ThRb8Qv7GM7PEQRXTsP+IAd8/hjTed5inbAug+jGBRkH5x8cXukcPCBc5UCKecfIraRotLGGJVrvUiIG41NVWRMtkSQZMF"
    "mteoEsBLnxz9Msfn8JdsUKbQqRgVh35vvPBxX/R30StQzA5OLz1l7ZN+scUx+m6F6YSNMEig6WHgfvQLWgcVG+KBz/HypjgivgjH"
    "NvIuFqgMYDlAvCk8hI3wqEkI4Se76QNxJYFLaSchhPxLxTMOAhYR5CvA86Z8wD71XQJ6h2qy/iFv4C9aczLSapYVPa0XuNM1pDP6"
    "90NPB30/8L0M84MJ4WC6GTx7/XuG/KDvGf3AwHcI+QP08k73RN8yPDs4THmBcqyHiTiG+T7ie42wzOuxj3P4rKHEMyx5yGfc1yyL"
    "OIfP4rXgoXzV912VDFpJQRW1VlaCSzoshUT9jNCPAx3727fv4PpygDzJzskSJcVlorwywLImgWVNHxgAXWOKPfjR50DTPz/zjFM9"
    "IzK/XLhIiTO1ZJMhXryhuss6yfSgvxn1VQP//vdb4ujRx6h9umbxksXi0EMOco/QR+wxcfbPnH5YahJZjdatLEtKuVvi19f8SvUj"
    "I0pLy326Q8+GggJvh96yMqcJBvOfLVr0tRg1qs4k/oT8pXTe+Y7oRBC7jbv/v7/8WUy+tW6+Yfg/8sijRUFhoehKhdd4Bv989hlx"
    "ySWXuEe45glx4YUXukdeNm3aJEpKSkXfvrE7dcdLVXWtdemmivJSmX+7lAk+Ozs7MhEtsP14SAawiGD2aJ2GXr7JBpp89GH5aJ6I"
    "ZhWC5QIVJDoS678C0Wdki/yVDeuI/lIjS5DtpYuwMHUFRkiir5cZpg7CX7Z4seqWgDhiMs94X56437rVq1UYdD/8uLLFG6A5CKPZ"
    "VN+cvHzRf/Bg39QHQQTlE/LDFh41KQ0YMiRquig/o+WVjTD5F/QMQbTPgtJK+Qf052/GBXOc4Tqcx3xR5khUPRy6R9A9QZi0Upjo"
    "C2U+02ifmVA8bPkSRLS81EHY9P3Q88kkWl4AfE7lPlo4iNeaVavU+wDlM9qIYJRDNHNS3Mw8jpWH9D0A+C4GvR+C0mV+FuZ+wHYf"
    "PS22uNjCjha3MOUvlYQSZ4BWBqiqqlLra9bU1Ir2lk6ZWF+zrLxClJYFDyk3p8EAZp8yU5wBVLhoP95/xDD3jNOZfd4XX6t9WFBM"
    "y5JZRZM4+3DmB2rkJoFmuaeedkaoIH5IdzziDHFDki684Fxx/f/dpAYBmPc2xVlJib+/C4xACGfVD6vEvkMGu2eddC5e7HwJYokz"
    "B+/df3Xl5WpEJTH1naniuLHeCSRlwO6OQzziLJVgXU3bZMUlxTtEVlams66mFGcQZi1VnDEMwzDNh7jag1DhkaupsVvGIGqypUCL"
    "hinMQNjK9LPPPnH3HI4Z41i7gLnQOTCbvOjOWKZDBx3l48GML8Itl4o93nD8OOGuNOawmnDaRHcvMcypNoYN9y/7k4icSY0E0nFE"
    "bxCRMukeg7BliWEYhmHSkZjijCo6qgAjlaF0sKaZQHjBOhUvhiHKOh8aWLrE25dj1MEHu3vhIAEHM6XJkiX24cM2zNiVlZaJh931"
    "AwnKu/jYrcyyf9UWnwVnn6tNaxFnsP9+Y4pn8AT6n3Xt4p3gNlGi6KakALEfNMcZrKRUFuWfBPObYRiGYdKL+FSUWwHCGoXmI/Q/"
    "M4H4wedmB/lYRLOOEGj63LHTOyt3KrBZ9sDLL70orp10tXKTrr5KTLrmVxG3R7fOauSnjj8L/OGazaObNm8Wl136S0+funvvvUcM"
    "3Xdf90gSIq/o3hBmPzvb6bwL0Dx6y611fe3SHfUsLOnFaGESZrpjGIZhmKZOaHFGlR+EF+3XWpo2ydKRkRnfiE3q21Zf0DFfJ0nB"
    "KiCY9BUAdGcj1r2ff+Ff4rnn/qm2cH/8w41qZQC9aRST0l55RewZjj+b/Zl47l/PRhyseOPHHe8RZuhX9+67/41YzYxHkJYE5SEG"
    "fqgfAVp5ZBiGYZjmQFyWM6oAqVK0Wc6oMs3Oii7OzLrU3g/N3akHtuk04rXqERgQsGNHieN2loqdxXXu60WLI7PxE0HNccRll17q"
    "cffd7yx9grnHJt9yi1j1w2o1Ka3wCU5/mtDZHysAkPvNdddFrG9oxnznnanihRdeFr17B49aSpZATh4YFOJPK6itdVYH0IUZCzSG"
    "YRimORCX5QyQpQJbLH5uY/eu2IMCTGy6wKxsbdMppIqYFb0R4V69eol77/WuKxdL68z5fK74/PN5aksOIzjfeWe6+N31N4gukaU9"
    "YosmiLm58+Z53OrVa9UyTljO6djjjJGZkkS0WEPrN9soTVBbU6Oa1qk8MgzDMExzIZQ4o8oPW+yprbtvG7WJSWWzMjPdIzuJVvIH"
    "GQMAlhorxwf1FzOhOcN0evWKPhdOLDAHirl+ZjT2HTJUTbmBLTlgio0wFq0ee/UQQ4cO8zh9AV5gBNvgQite8CyD0q4PBiAHzLxj"
    "GIZhmKZGXM2aCln5UbMmXHWVbVCA0+8Mc1AFYRNR/n5o7o5Gv37eNSVX/+Bdz85WmSOeOvCxZLF3eRWIqnjXyzKFAO794IMPq8XJ"
    "k0mAPkkJ6SRtgqxmGAxAFjPdMQzDMExzIC5xhgqQKsWIOAsaFCBdXk58TZtm/WoTcIOH7OtZFBzLOG3dusU9Cgf6MS34cr575HDS"
    "SSe7e+GxSYeevXqrtTWJxERDCDVmBBtGwDWkyEsGQf3NqqorVdlDsyYLs4YH69Zdc+UVkdm6kwHCQpgIO5lgXTyEG+T+fOtktW4e"
    "Zg9vKVDa05lUlAcqt2Edyk66Q+VbjyvFn2naxC3OaAunxFmVfSUA9DvDcjrxEEY8FOTni/+74Ub3yGHunPgX3J46baq75zBhgne9"
    "rFDNo0lSO+Z0Gj7lZSPErU3N0pS0GbI2yHK2q7bW8yMBsEALJlXCpzmABaGxbh4Wp25uAo0raYZpuoQWZ7owQ/MjKkWqGG39zmpq"
    "d4mMzNZqGaYgEp1O46STT/NYz5588glRXl7Xh8ycTsOs42d9ONMzj9g9d98tuoRYM8tMiS26iUgE8xqbKMGSTanA1DRhn0GqwSTE"
    "trhg9C36m1H5Q3nUyybD2MDC0VhmS3d33n2PWoAaYFHjt9+YovabO1icnBZpb0lce/0NvjKAcgGQH+ZnDbXAdX3AGpKIO7ZM8yKh"
    "Gr+VWzHCoWmposLfuZ6aNrHWZhBmXWqzVpkVLrzk5+WJx5+oWycSQuuJx7zrHeroU0+gCXTSpKvdIyEmTpggzj73gsSsSiHiG8YC"
    "l4ggsl3hkyYJJSo9CGrSRH8zGqVpijOGiQcsdHzc+PHi8MMOU8fr169T2+YOREdTEB5MbLC4N55l0MLmTNMl5sLnOiS4UHFijjO4"
    "iooKtQh6h46dXF91ZGIiWhn6tqJi94wXWNXMZZrCLoAOPpo1U0yYcKraB488+qg486fnuIubeyt3XAFh9n+/u071UwMQZg8+9JjI"
    "z89Tx2Ylj8XRTz3V+WUNLr7oInHf/cYSTUZ8EYaZo+TjggvO9Uwwu+ibJaJ3r97yGuSte9LF1BvIF/1RzZkzxzMyFFNp3HDjTRY9"
    "ZsTP3RLmfRTuSdvC5xdc4Cx8br0uSUCXVWIOPX9iRFlpscoLWuwcTecQa6AhRFo6LXyOuEx5/TXVNEcMHjRInHn2OWrk8A/ffy+m"
    "vPqyKC+vUH5yZZ51776H2HPPHuKs8853r7CDJr5XXnhefPHll+4ZIfbo1k2MG3+SmPnB++L7VT+IK6+8ylMpfDl3rpg+baonPgfs"
    "v7/46TnnKiEUDcpXWDJg4SBwfvq0d9T9dMKGi744M95/3xeuDuL99NPOjz08S8q3gw8+VPTo2VPt4/6wUJCosaWV8mf/UaPcM8IT"
    "FvJ01kezRNEOZ5WT9u3aiV9cepnap3sQeI4X/OKXvvQhPfPmzYuEAeB3/Ck/Eb3cgUjoQwehSeGRdWjimWcpP9S8bebHpx9+KN59"
    "d7ov7DHHHOt5zvA3Z85slaYtWzaLjz/+WFkeAdJ04onjxGFHH62OYxFUZgYMGCheevklz3OjdFE6dPQ4hb03QF6Yz1ZHDzcvP1+8"
    "MeV1lT/kf8vmzeKdN9/wfE8A4k3xpDIALrvqat8zpXv067dP1PKF7+/IkSM9311buqkpu7HeS0xyiNtyRhUgBBBZznbtqrWus4l5"
    "yaI1bZqCJF6OPGq0+PjTzyJNnFdcfrm4/rpfi7lz56hjYuuWLeLll18QY48bExFm106a5BFmJmVlZeLZZ+uscwArASxestg9cgkp"
    "CBAnc1H0V195SW1t+WAKDd0P4vbgg39zjxyekULqe/kSiIUZ3aBnsGnTJvGCrJx1cIzzqUZZzSzxguDG5LMRy5lMTEMIsnQEL2WI"
    "Gby8USGiMsDLe8m334q7/nyHqjTKpRhAxUMveFSgOI5lIYKIuP+euyMVDsKGQzgQMRs2/KjO6yA++Ax+IFLgHyAMhJVIfy4SbIgz"
    "pRFhA4T77JP/UPv1ZdlSZzoeijPl27JlS8VDD/xN7etAIFFa9byn/EFeEBQWRM9b77ytzpF/VPIIn+6B8xQHPEczfRi8AKGJ6/Q8"
    "hl+EAREAdGEGsA+HuOjHOs888bgSQwjbLE94BnqaIMhw/ZtSlCA+ubm5yj+uw/UIB88uFnqZoXtii2eLMEwoXZQOHYoTtsmEwl24"
    "cIGKK9JHoEzju4b4Iq8Qf3omuAbPBECgbd9epM4tkMLaZObMD9Rnnd15LW35gueN7y/6R+qd/1OVbqbxiUucUUWottJR0xIqy8rK"
    "CvWZDlnaCvJz3TNeEp1OQ2fQwMFSoM1VVjNYkiCgjh97rOjUoW3EDejfVwk3LP4N69ens+eImyffbhVmq1fDz/liz+5dfWIKHHrI"
    "QeK0004WTzzxqDo2pYFu3QKPP/awGDZssDjmmDHumTpuvfVWUViYJ665+iqx6odV7lk7CHfVqlXivPPOkV/iTr64IW2DB8tf0ONO"
    "EA8/9Hf3bPw89PcHxYknjBV779XD0y8P4Hgvef4E+fmDDz7gnk0+mCfPRnVVVUSYYYvmdU+ZbCFAeKFiBD8762fitr/cqawLk2+/"
    "I/ISf/XFF5S1A7+eYeECeMnjOMiCRMBihooBFc51v7te+Ye7+dbbIuHrID5UmeJeN90yWflHny74R1gIM14++N/7agtLCqURYSPN"
    "AMKhvkBEzJ/vjNzu0KGj2hKodJFWWEmQdlg1IIAgSACaQyled913v4onQF4gT3RQqevpwLNC/lJe6vlM/eD09KFCRj6Ciy662JfH"
    "COfJxx9Tn+O8bjXBPlxQ0xesNEgrwL31OFKaUN5MgY176mnClsTJwgVeS5IJwqIybIZB6U8n8CzwvFD2VF9FWRYgopAHyH/kFeIP"
    "h2dJz5ZE6r7u2sgQeTooJ/RdG3HggeochDzQnwWeN+XLihXfqS3TvEmsz5krzLBFJQlXXmb/ZQzrWXacU2rohOmHlpeXq5ozX339"
    "LfHlwkXiueeeV2JNdzPe/59Y/t1Kcc9f/yYGDRosxY5fAEAY4tcLZuef/dkc8dlnn8ut3/35L3eJ408Yp66JJR5PPHG8ePmV18Sc"
    "OXO9TlsV4LIrrhBdjQljZcjutg74ueHG34vP585Tbq7F3SVfHOPHn+ReYROP7k4A4086Wdxzz1/FvPlfeNx8zeHzk07yvkCTJY2g"
    "y4LnN6uK/CBAGWhJgkxngaxMqWLUm3DQXDLpt79T+6hMErFWgcWLHevwaadN8DQfoal0oqXpB806AGJFFwCIz6WuMKQw4yEvL09V"
    "9mOM1S2oEosHWPvQhKW766+dpKxCyEtUjifL9JqgQkRFjLSDD2a8p7aIl9k0fOEll6qKGrz/n3fVloAFBJ8TyBs0MQM0Ven5jH5w"
    "JmjKBBCKerOpnscQgGEsViafzf5UbVGe9HsjbDQdI+7II916Bsw0gdFjnIEGsayzsCAhTFsYiAOJwnTi4l/8Un3fkC8EysHo0WM8"
    "5/As27dv7x45HHvCiWprfi/xXQZDhgyJhNGhQ3sVrlkO9urZ091jWgIJizOgN20C26hNNFHBf7xznkXDrJMxbQex9949xYnjTxFn"
    "nXWO+KnmDjzwINGpU2fXVzCYiHbw4H2VGzR4iBhiuiH7qm2vns4vRJuI0sG8Z7QSgO70VQHgCrQvN7CJKMRtqPwFFnHGigDkemsv"
    "elM1xdBmagLdYcOGxXR9+3r7fMQKNyw1luZxgGZzNJ+T5YyaNFuiQPt60VdqixHKsKjobob81Y0KD6wO0cxtgsodlSaw9d2B+KLw"
    "ie3bt6mtLT6fznIqdIQZr3BApQ2rAfXbgYUHYd55+59cH+HB/dH8oztKJ/pVXXXNryMCjIBgMytISiv6+Ng4aNRBamuKE1S4QQwf"
    "EVuIUHPaYUf5nwniTRYraqKNB+oOccihzsAIHQgGsvqsXbdWbQk6rwNBHYY1a1arrS0MECZPGhKIbtPyiLKB8onvCSxgKN8onxD+"
    "ZOUk8IxIuOtNm5/P/Vxt9fSSBQ4gTIhi9Ld74fnn1DmmZZBwnzNVMbriDA4ds22/1CEydtXuErl5Oe4ZL2Z/NLNZMFHMqSeCmsri"
    "xZQCtugmohfChZuAlg6RnWZ8k/UM4kWVlQCrWXW106RJrqU2aergVzia2ExHFfna1U4FmGxMoQGhA9A0ZotPouB9gr5Q6OB87913"
    "qX44CA+DkOIF4oWa90x3hRRmuuWKIMuWDvoOgY6d/AOgQCqsG7qoNQUkgc7kiUIiNc/4gUiQ4CJhSoQVYjZIvAaFUZ+wU0G/fv3c"
    "PS8QY7DA3nbLzcoKi/KJ7wOEvQkJd2rapCZN/NgxB5E88sDfVLlHmGgmR1+zRMo903RJyHIGlDiTjixncKhAbc2FNVKcYeRmtOWc"
    "iGT0QwuLGW6YaS98WK6ROePuOaRsOg1LXiciU5KU7HoTNLcZwGTHKGP0Y4DKX0sGTVzo4xXkRmgv/GSC0Z86ZBFAE6AtHuR6WgRQ"
    "NGAhg+BD5UVho+8X+nc1FiRM9XkVdbZt3eruJY/Obv5GY9s2r3BKBFtHe53c3OQJJrN/X30Jeh7JwiYW8cOBfnygSR/lE/3NIPht"
    "wp4s0dS0SU2auvUQ5zGQAH7wg4LKPfq5oVmVaTnUX5zBuQIN2wrjxQ1Q4aLpMT832z0TjLVuNupg2xxYZkWdiHawCYNEwpWpdfeC"
    "MYINKXbiT1WYuITBjG8qsI34BVVSmOH+9COAyh4wn09LAFNhAFRIaGoxHSxmiTRvAV1A0eg/Hfq1r9OhQwd3z2n2NB3iAqf3y4kF"
    "rEWwAMICccMf/qiakBAWLEc2C31DQQIlqMM7RniCZIoPpJksMWjatbFy5Uq1pRF/8UDiOqjMLHItdz16OOUuGXTs6OQPhW0Sa0CB"
    "yYoVK9y9hoMGUUA0of8hyidZYM0fMADlH03oAE2by79brvapPxrQ++KhaZPKfTzfHaZ5kJA40ytGNC9RpamaNstK1Gcm1TW1amCA"
    "2YwZ0IoVN2YVHUbAJYRNRaVIIJjxDWNdC5OdZnTDCMMwfuqTCzU1uwKbNCsryz3CjCxnLRXqn4JRhqaAwjGmbMAv+ngX8geoBKj/"
    "0vP/fNYnhDAK1GT48BFqizm8TP8QWYgLdWiPF0zTYFZM+sjPhhZqlFZUzGbeI61UYdv6b9UHdBgHmGfLTDP6I5GQtQ2WiJVH1NyG"
    "+crMNKG/E4lxW3+3RKGwELY50ABxoBG0OiSMTRGJfDd/MDQkpmVTzzPTokflAnOTwToGYaw3VdOUGCj3JpjvD1DTOtO8SdhyBpQ4"
    "cytLvfK0tY1DWKDvWWGB1zxsExz+fmjuTj0xK/Rk9UMzsVvg3J16YM0HX7ixbxQmP81QwjyCRB8T4oOmbxvKmiY9QPirciYdaMni"
    "DL+k8Qscv7DRBILKGX1fsKW5ldDkaYoaGrEIf9HA5JkAFQyaFhE2dXRGhWKC5hpUMhAIWKNSjw/6zICjjjxKbcNCFR7CxH31OJAA"
    "Asma6ywsSCuJV/SDQ9MW4oUtpRWf4xklE4wkhfiiPNbzA/2RwPFjj/c8cxq4gXnm4M8UXgQ9P7M80dxnAM12Qf3dEgFh0coMuAfl"
    "I5Vh6genQ8IYYl+PI+V7Q0P5+8Bf7408Dz3PACaS1adVQd8yPEfqp0nCmKBlmPDdQ78zCvfmG2+IXIMygPswzZt6NWvSFo4EGirR"
    "ivIy9ZkJKmCb9czEFA9hptNIVvOdr3+bu41KKE/ecIOsRF4SSJM1r9ydNAUrTARZBSsrylSZioh/Wc5Q1kBLFmiYPR7TDaASQ+WM"
    "Ckt1GpbHqPRopnGApkqqfPGCjzXNAZpmMJcWiQGEDYdrITyoGUwHU3jgMzM+AELRHPUYC1TeNJ8Z7qvHAeFRxWgTi6kGs7xT8xSE"
    "IuJFghF5j8+TDfIDI0rpOer5geeEvklmHh/oWtFQ0cNfUJ8yCDrb89PTFGtFiURAmCTQKB+pzNim0tCFsR5H5AmF05BgdQfzO4L4"
    "oGxQ+UDeb3GtaASmTiGoHxoBUU9pR9mmcGHwwPcB9wP0bJjmSytZKSagABxwKRyaEGtqatRyTlVVVcqU26ZtO5Gd7R+xkpWZocTW"
    "9iJ78yfIzMDyS95omdUwKmhf1I3K2vFTZ5HBguhmJ3qzgneWfop+b3UfzY8Kw+/J3TpA9JnxNe+NpaD0aUGA4cVybNHXPj/BS0oR"
    "/nDlNe4+EeuaREC8KqtqfHkDYDUrLdmhTPxYrikrSwp7V6QBM/8aAjShmL/U0QG4scCv8mWLF6vmkL179hJ79+4daOGA5QQVNEbl"
    "2UYn2kB6VX+xvHzRf/DgyLQWCAeiz7TO4bN1q1dH4jNQm78pGmh6w9QfZtzM9FF4OI9pOmBpiGalgj9UjvGkOSguJnrc0NdrgIyb"
    "mffRwoqWj8h3YEsbrlu+ZIkokz+CkX7b9QTdH5C/WGHHen6Up7BuxpPeIGzPGETLNz39SEe0OEWDnkHQdbHCRXqXyrivWe3M8E9l"
    "AOfRvNlJ7pt5GCaP9OegP2PEBwMJMCo4KN3Rni/TdKiXOAO4HOIMFSkEGsRZpfz1BctQe0unWFSo2dmZ8tdGqRRzNeocLGn6GpvK"
    "emWKBXdLZEDAGUKmrHKX+G5jXRt/u/xM0burt+3eDEeJJncfhBFnjthx/GzcUSWW/1gmjhxc1ykaQDTpWQtjoR7sxqIqeW2lWFdU"
    "KcaPcL5UQeKspKJWfLehTCzdWCrOPmxPUVxeLb74fqc4oE9b0SZXChVToBkRbiX/eUP1eZFC1hs/hbz51PmbxIF924luHXIs+eDu"
    "1IPqalluApo0sY4m7mGuo4n8bwxhBtJNnDEMwzDNj4SbNXVQUcJKpTdtYsJQjLIzgWDBqgFtCuxLOgFbE6W5IHqQppzyzWZxzBuL"
    "xfn/XSGKKxzxFw2zko+3H9rfP1orTnrnW7Hge3Nxd2/8DM0l3lm4SRz+ytdivRRoEQLSBGF2+CtficnzneaoR2auESf+e7E6b7vC"
    "J1tC6BjbrTdurxQTpy8Rk6fbR0IFRDc0uL4mIL8h9mkdTTiUrcYUZQzDMAzTUCRNnJFAo8oUAg3mWxuoeOEnaGqNMJW+rc9WYV6m"
    "KKp0pmO4+5C9xH692qr9+hJNEPzqyL3EE0f2ESP6tHHPhKOo0hGOYwbWWReD0t1Gpgucvhf62ewWczeWiJ6FucH3NOJrE7JhNA6s"
    "ZVPGDRaTx9knYKwv6GtmVZeSivJSVYbIWkbiDLBAYxiGYZoz9RZneoWpW87IelZe5h8coCwmUqDl5+f6mjTry3M/OJMxHtG/vby/"
    "1yrz9Efrxa/fWCEmTflOnPuivyPxwlXFYvLU78XZLzjrAP769eXiqVmOtQrNl398Z6VyV7+2TJRW7BJPys8mTV0hPl6zM6J2Xpmz"
    "Udz89kpxzD8Wik1FVeocgebJP769Qpz13DfizsWbRC8psPrt4Ux38MpnG8Qf3/pODH5onljxY12eIV/nrXJmfD9hYKeIKH382L5q"
    "O2vJdnHlS0vE799cLs589muxYOUOMXX+RnXuif+tERu3V4nRj34pFsrz4KPF28Td01eKIx/9Qkz9YpN46dP14sxnvhJXvLhYHeP8"
    "LOkHza5nPLVQTProe1Es433TlGXiiEfmixc/Wa+2sNrZCCub0JIZZDWrqa5WZccUZtgyDMMwTHMnabUdKk9ToKEDd3l5qRRj/koY"
    "TZuQGYWF9rmYfPOh2etxD58sdeZ/OWGPtiIffbE0Xvt8k7hp4QZx7eE9xD+lgNvsWtj0ZszhvR1L1PQNO8VKKZA2VVaLhZvLpFgq"
    "F/s966xneMbQLuLZVVvFrKXbxMBuBWLahh3iiL3bijIpYCDKHlm0UfRqmy3mbvNbDS957Vvx+poicfWBe4qK6hoxUVnChBJlt8xf"
    "Jw7t2U6sKa2UIs7bHPvI1xtFblamOHKQ06/tVwf1EEcN7qDihebNk6Vo+2RjiXhnfZHYp3uBOHpwR/H0yi3i+WVblP+FxRWqb9s0"
    "Kb6Of3OROF76/3xriVgir9mzfa54W173TVGFFGKr1PlvfywR3dpni4U7nSlR9umeLzrkZKrPHvpqg9oW5nnzlwgjs5U4r5FpDPBc"
    "4Y7QNMUZoC3DMAzDNFeS1qxJW1OgYb+01D4yE81aWVkZIifbvyi62RIXph/af7/brrYT+3kHImzaUSUu+2SV+L9BXcXSjY7F59J9"
    "7SN6erZ1Rpiiv1rXnCxx8chu4v6P1ygxhSbMeat3qs/b5GaK/yx3rHRHD+wgpi7YLO7/dqM4smuhuPHLDeKlsf1FVylwiOny83ek"
    "kLv3sJ5izmrHinV8/45imjx/n7zujL3bi59/sFLcOqKHFIl1zbEbpaiau61EXNGvbi0/CDNw0muLVfMmxNgc6efgjoWqabdAxu0n"
    "e7ZX5wpzW8t0ZIrBexaK09/9Vpwiz//6vyvU9vIxPcV/ljoCrqu85tL+zsLwxwzurCxjq0sqxJk9nXu9tdrJ2wdP2Ees/tUhYo/2"
    "/pG4YcFzD5pKpLISgnC3EvaqHLnCDPvpAEZFqakhNMcwDMMwySTpljNTnMFVVlSofmYm6AuFkXptCvN8lrJEmLLOET1HDXDWv/t+"
    "Y7mY9MYKMcu1qI3au424d/4GtX9AT3t/tD1dcXbnp2tFL7kPoQRL2d4FOaJbu2xx3+JNESvW4yu3qfMA1i0wcWgX8f3lI8VITWCB"
    "2Wj6lMBShSZNhHGEDGOaK/COH9BJfHPR/uL8g71LpMx1myOHdStUWwLNjhBPZ+zVTrww20nT5cP867ld/PISMe3MfcXnK508GNuz"
    "vXjy1IHiQekKpSB7dU2RisvTPxsiHl++RYk99HGb5/o/vFd7UVJeq6xlEHT7921XP2FW6zxzG7t275JlpdwzZUZr13IGULYaGwxX"
    "xxxiumMYhmGYZJJ0cwQqUlSisHjoAm3nDvuSE1g1ACKtjdG8Ge+oydfmbRLrSp2Rj8s3lolnPl4vDn9tsRjRJV8Uu53vb5u9Tmyo"
    "cvYf+GSt2gK90u8uBRj4+b5dxW/G9lT7EGDD2uaKVz7fKDZX1YrZP91XrJTCD9a0btmZaioNYv7qHeKGt78T81ft9IRb5DZV/vnj"
    "1eo6AGsaMeeHHeLvs1aL+d9784nE20cyXPRZA5img/ZfW7tD3LPoR7X/6Nc/ih+3O3nQSQoviK4/n9BP9Otel7fvrS4SUxZsFP/8"
    "bJ1Y4VrH/jB0D9WHDvuguLxGvOY2ia4rqhCffOvE4aLh3dU2UZzmTL9IJyrKMAigrsyg/IB0EGUMwzAM01DUe54zEwQHZ05MixmO"
    "c3LzREGB1wIEUPmiebO8vFKUljniAvWxWSnDuqY3h9HnEEofLndEjVmPnzK8q8jLbi1emfujGNmzrdiwo1KUVNaKcft1FgU5jjbV"
    "5zZDEyjEFqxaBPqffbhsuxRuOeKA3m2VBQ33/seHa8WYAR1F3z3y1ICBqV85YutkeU/02cKktxQuwvhg6TY1OnP+DzvFyF5t1WCA"
    "zTurxcwlW8VOGSd8hv5d+hP56NvtYtnGUvGzQ7qLQrcfHQQw+vG9PNsRZQP3KBDzZJinjOgq9ujgWLWmfblJjOzTXnTr4IjNUim4"
    "PlyyXYmtHu1zxfgDuqpBAnNX7VDNmBBwL3+6Xpw8spu6DwYFoGn3JHm8YMUO8bn0d+oB3SLh65h5HkRVNabHsItuDAKoqChV85lh"
    "XjMSaCT2zbLAMAzDMM2VlIgzQBPTwtHEtNi279ApYhHRQf+xLFkZF+2sm5zW7FNmijNgVtqozPVJZEnI6JjVvHXiWTNceRwrqzCJ"
    "rA7CMC8x7400xghW+nGsToRzjRlfrxFUTWjrC9hMkzdcq/4xTobwYgXNmfRcTdCcWVq8Uwr0zMhKACTM4ACLM4ZhGKalkPRmTapE"
    "qWKF8EFFSxVu8U6nD5UJRBem12jXJl+JMJBQhWxcY06nAajCJ2Joo9CY8U1WuDJkd+sQ1JleJxHNncAlVsynVgthhtGZAZSVlkjB"
    "3jpSRsxBACzMGIZhmJZE0sUZ8Ai0jLpJaVH5wopVUuJ0jjdBkxfEVNu2BcpS5Wq0CKHmQ0tAYdgEXFIEgSUuiYUbIk1msEnKqgSC"
    "9fjBM6uKMm2GGp0py0REmMmykm6DABiGYRimIUmJOCNQscLpAwNQCWP0pm1pJ4CRfBBm7dp6+14FYTZ9ms2TiWJKgjDhhhI7RsA2"
    "K5jZPBoqSQncO9Ug3lg7Myhu6JNIozMjwsy1mrEoYxiGYVoqKRNnVLlSZUvNmyTQ0Lxpm5wWoHkTFXV+XgJTNliUDDrm64QSOyEw"
    "BUSYpsRE7m27JhnSxRaVZGqi6prawDxBP7PyshJZFpwyQeIMecpWM4ZhGKYlk3LLGdCbNyHM4LC/fbszRYMJ6nNU7NnZWaJNQZ57"
    "1iEZ9TWEgQmsdTqJ9Nmy4Qs3jIkrzL19gtMudD0kcOtE8yHayEyAaTPUIBDDasbCjGEYhmnppFScEaho4VABk0DDlAmofoPmP4Mo"
    "gECDZSUvp26mfbPSjiYA6oOtGTOmYAghZGxefMHGuo8i9r38oSQmtGKhpwn7MYVZRbnA2pkkzHRxxqKMYRiGaemkXJxRZUtWEVTC"
    "qIxJoNXUVFsXRwck0PLyskWuZYmnIExrVbL6oZmEsSqFspQZ8d1t64dm+gmVJuMad6tjaqH6ZhWeVzRhhgEA1VUV6tnrVjOkj9LI"
    "Ao1hGIZpyTSY5Yy2SqBJRwINrqysJIZA2yXy83NFXm6dBS0qRuVuEzLUfEbUU5NEMIVFKBGVgCIKFWySUhVWKqHzfzRhZg4A0IUZ"
    "PQ8WZgzDMExLp0HEGUClS5WwPr0GLChwpaXFyopmA1NdKAuaFGe5uSFmqE9A7CRrOo0wdzbDDWcFC+HHlw/uNgoJZJU1WAizoDUz"
    "AYRZaYkz0SyJ8kxZBlR5YGHGMAzDMBEaTJwRJNBInJEFDQJtR9H26AJNCoBsWbkX5Oe6Zx3MSt0mtBLBlAqh+qGF0VDmJZZrzOk0"
    "/LGxkMC96wtuCeEcRphhgAcJMzx/ms8MecjCjGEYhmEcGlScUQVMlTEJNBJn2EYVaFLFYAkgLI7drm1BXBW6OZ1GmPlsE8FmBTNj"
    "GcZaZV5jnQ/N3dYHW1TMbA2y7OF5VFXVRG3KxMjYinKsmVknzKg5k4QZwzAMwzB1NIrlDFDFbFrPYgk0yISamlq13xZLPclKPhFs"
    "U0/4p71IAJs4M8INM0AhVFNniOk0fNInoUT5wcz/sGRGiyeEWVlJsXxGztJM5ExhxgKNYRiGYepocHEGTIEWrwUNcgBNadi2bZNn"
    "rdwTqu6NcKzNowkIiTAd8xMIVhK/0goTl1i6UK2DivyP4hFNmSXFO6zCDM+Lnpnt2TEMwzBMS6ZRxBmgShkCDS5egQYgEDCSs7Ag"
    "zzeS06z0a8P0QwthrTKlhFWgJCI4jGvswcb2YxLCiy+60cKtRZ5X19jT7VJbW+t0/nefJxw1ZSINeN6AhRnDMAzD+Gk0cQbCCLSi"
    "7ducxbEDcAYK1Ei/maJNnM2cJBKIZPVDMyVHqCbKMH4MQoWbJGAtQ/+yaB3/ga3zP4kzFmYMwzAME5tGFWcglkDLycmRlX2xKCst"
    "Vf5sQKKoZk4pIAryc+Q14Ses1bH22UpARITRTGa4tg7/fhIQY5ZL/OLR3QkAHf5jWcsARHRpyQ4llHVhxhYzhmEYhglPK1nhJlDj"
    "Jx+KBixhcGgagxUGrrq6WlRVVclKHtaxtqKVYfHSQad+9HNCh/WKiipPcyZmp9ATi8lwzX5lpnBQfows8kkLXKP58U+DAbznEE8z"
    "6817Ixx9tQDjY4V5rpUxSEDh84N7uwcuZtAIF17QdBxGOJaVlshnVu0RZdyUyTAMwzDxkzbiDOgCDfumQIPDZ23bdVCVfhCo/jGH"
    "VmZGK1FZWS0qqhyrjyO0DDHmbolExJkjdjQ/8tjUIKYgCiPOsDC4KYzMcCF6dItfKHEm/3lD9XpBPJDP1WjCNOJogvxEMyauh6WT"
    "rJ54PnCIH6XLTB/DMAzDMH7SSpwBig4JtF0QaK5II4GG/YKCNiIn1zsZrQlZ0UBFVbWordkVU5yZYswmKMwz8OMTWob1DPOshRF5"
    "Ojg0LlHndExxBkyBpsJx90GQOIM/aEGI4jDWMjyHstKdSoTp1jI18z8LM4ZhGIZJiLQTZ4CipMSZFGkQaGieJCsamjgh0rKyckSb"
    "tm2V32hApLWWIk1Zg6qlyKtx5kkDpmSA0IA/Hb9oksd6tpnHElOc4Rozp817w1IWI1h1Tse5xrh3DHHmUBcQ3SesKAMV5WWisrI8"
    "MnBDiTK3GROijIUZwzAMwyRGWooz4BNo0kE8UFMnWdHweZs27USmFAixgGDIdPujKYEnRZrZvGhtxjTEha1J0qQVLHaan0TEmQ1T"
    "jNl0j69p06qNqOm1lZuvXkEaBPyWlRWrIHVRRsIM6WRhxjAMwzCJk7biDOhRgzjDsU2gweXm5omCwjau72AgFciyAxHmXF/jfOhi"
    "CgrzOBFx5mCG4/WSiDgDpv5RAyZ0L8pD3QknPa1ci+TumGkhHGtZhRRlTr8yXZTpwgywKGMYhmGYxEhrcUZQFEmgUTMnRBqJM4g1"
    "fBbWigYgJGApg2aqrqoWVWo5ol0+YWHthxYj25wRpaYfb7g2kRdL1CBY89bmJUGDAihsWMnUKNboSYigW8sgxkiYkSgjsUvhx0oD"
    "wzAMwzDBNAlxBiia2NqsaOQg1LKzc0RBQaErkGIDkQS/Ga1byTCk4JMO4RJhRmwqhaT5UQLF78ndOoQRZ/WeTkN+iM8RBgRZ2D5l"
    "AIMnKivKRZWyljmCTBdmJMhYmDEMwzBM8mgy4gzoUTWtaLpAg4O4ys3NF/kFBe4V4XDEBgQNmv1kuDIcCBqfiHK3BPx7/MhjU6c4"
    "ftwDibyN5xiY4sYUZ8AMF+LInE5DXScv2+0KMlNcxgLNl+jwDwHpa8KU98NoTCev6oSgGXeGYRiGYeKnSYkzgqKMLUQaOZslDefz"
    "8gpEXn6+uiYWFLYSHq74wD6sSFhXEk2CEDqmDIEfMysbbsQm4og9+UfuQLAijvp1YR9zdXWV6lsmr4hYyiDIsI/7YF/ljZsvgLYM"
    "wzAMw9SfJinOgB5t04qmizRs0dQJ61F+fmyRZssOJUakg9hSTZHynGoelH5V/y15D0d4ea9NhjizoSx7cDI8AP+wkOGyoGbLWI9Z"
    "ibIKKcqkP7KS6YLMbMYkKA4MwzAMwySHJivOCIo+thGRJrdkSSOBVmdJiy7SwmSHEigQJdJhowSbuswRa0CJJPmZak50w4xHnGEL"
    "qN+cOnI9qyCRRhW0EWAAQf4q0KesqkIFqlvJSJBREyZgaxnDMAzDpJ4mL86AngTs6yINwgxbU6Th85ycXJGbl69ECJFodjjiSYo1"
    "tZF/se/qF5+Qcf1F7uXZ1DVHkjVM7cuTCUZNoacLTbRouqyprlJxIzGmizIIMd1SpqfBlx6GYRiGYZJGsxBnhEeAaAINW1OkkcNx"
    "ZmaWGuEJa1pDZAdJG9yqoTIf6cKoSzRf1tRUR0SYx0pmiDISZgSLMoZhGIZJPc1KnBF6kkicwWEfjoSaKdLgJysrW2RlZyurWqpp"
    "iJyvra1RTZcQZJBWuhAjMcaijGEYhmHSh2Ypzgg9abpIQ3OhM+dXsFiDPwg1WNWwwHoqBEoqch7xrqqqVE2WNVKYkSAjEabvI03o"
    "U4Z+bSTI9HSyKGMYhmGYhqdZizNCTyL2IcQAiTOc0wUandf3HUGTqaxqaAJNhnBJRs4j7rCKKTGmmmxrIuJL35KjYxJjgI4JFmUM"
    "wzAM03i0CHFG6EnFvsdBhMktiTGbI7FG4UCsZWRmiuysbLUlsRMWN5jQ7NrlWPWqq6rktRSfWnXfaI6sZM50II4Q0x2h7zMMwzAM"
    "0zi0KHFGmEnGMUQX7ZNQo/MkyCCGzHP6Plyd6JEiSAohQCJJIf1EkH5oZn95hdqq+0jBpfZVuHVWPoSLcPQtCS99n+6n9vGZu687"
    "HfOYYRiGYZjGo0WKMx09+dgnFzmGQJL7uhgDpigjR5+b+7YtQeLIFE4ksPR9chHxFXDedIC2QN9nGIZhGCZ9aPHijDCzQRdSnn0I"
    "Mu18LEfQvn5OJ0hAQWzRfhhn+jWxnWMYhmEYJn1gcWbBliW6uNL3I1ucd/etn7vo+zq6sCL0c8o5B5FjQj/WzxO2cwzDMAzDpCcs"
    "zkIQlEV0HlubH/3zCBZ/CkNs6VsdnIv2OQg6zzAMwzBM+sPiLAFiZZn5ebxZbIqrWGKLxRjDMAzDNB9YnCWRVGclizCGYRiGaf6w"
    "OGMYhmEYhkkj4ps1lWEYhmEYhkkpLM4YhmEYhmHSCBZnDMMwDMMwaQSLM4ZhGIZhmDSCxRnDMAzDMEwaweKMYRiGYRgmjWBxxjAM"
    "wzAMk0awOGMYhmEYhkkjWJwxDMMwDMOkESzOGIZhGIZh0ggWZwzDMAzDMGkEizOGYRiGYZg0gsUZwzAMwzBMGsHijGEYhmEYJo1g"
    "ccYwDMMwDJNGsDhjGIZhGIZJI1icMQzDMAzDpBEszhiGYRiGYdIIFmcMwzAMwzBpBIszhmEYhmGYtEGI/w+kfRMfeaqciwAAAABJ"
    "RU5ErkJggg=="
)


def om_logo_path():
    path = os.path.join(tempfile.gettempdir(), "om_logo_ofppt_v2.png")
    if not os.path.exists(path):
        import base64
        with open(path, "wb") as f:
            f.write(base64.b64decode("".join(OM_LOGO_B64)))
    return path


class PDF_OrdreMission(FPDF):
    def header(self):
        self.image(om_logo_path(), x=25, y=5, w=78.85, h=21.96)

    def footer(self):
        self.set_font("Times", "B", 10)
        self.set_text_color(0, 0, 0)
        lignes = ["COMPLEXE DE FORMATION BERKANE", "Hay EDDAKHLA Bp 184 N2 BERKANE 60300",
                  "BP 41 CP 60050 Tel. 05 36 61 278 9"]
        for i, t in enumerate(lignes):
            t = clean_str(t)
            self.text(105 - self.get_string_width(t) / 2, 279 + 0.891 * 10 * 0.3528 + i * 4.05, t)


def build_om_pdf(personnel_data, om_data, nom_complet):
    """Construit le PDF de l'ordre de mission (positions mesurees sur le modele Word)."""
    pdf = PDF_OrdreMission()
    pdf.set_auto_page_break(False)
    pdf.set_margins(25, 5, 20)
    pdf.add_page()
    K = 0.3528                                     # 1 point en mm

    def wd(s, st, sz):
        pdf.set_font("Times", st, sz)
        return pdf.get_string_width(clean_str(s))

    def tb(x, base, s, st="", sz=12):              # texte positionne par sa ligne de base
        pdf.set_font("Times", st, sz)
        s = clean_str(s)
        pdf.text(x, base, s)
        return x + pdf.get_string_width(s)

    def tx(x, top, s, st="", sz=12):               # texte positionne par son sommet
        return tb(x, top + 0.891 * sz * K, s, st, sz)

    pdf.set_text_color(0, 0, 0)
    pdf.set_draw_color(0, 0, 0)
    pdf.set_line_width(0.18)

    num = str(om_data["num"])
    yy = datetime.now().strftime("%y")
    date_jour = datetime.now().strftime("%d/%m/%Y")

    # --- en-tete du document ---
    tb(25, 35.5, get_etab()["ref"], "BI", 11)
    tb(73.3, 35.5, "N°", "BI", 10)
    tb(85 - wd(num, "BI", 11) / 2, 35.5, num, "BI", 11)
    tb(92.2, 35.5, "/", "BI", 10)
    tb(93.2, 35.5, yy, "BI", 11)
    tb(131.9, 35.5, f"{get_etab()['ville'].upper()} le :  {date_jour}", "BI", 10)
    tx(75.5, 41.0, "ORDRE DE MISSION", "I", 20)
    tx(50.6, 49.0, "OFFICE DE LA FORMATION PROFESSIONNELLE", "BI", 14)
    tx(65.9, 55.0, "ET DE LA PROMOTION DU TRAVAIL", "BI", 14)
    tx(88.4, 62.0, "D E S I G N E", "BI", 18)

    # --- tableau principal ---
    X0, X1, LX, RX, Y0 = 25.0, 190.0, 26.4, 130.1, 72.5
    transport = om_data["transport_type"]
    matricule = personnel_data[3] or ""
    hd = om_data["heure_dep"].replace(":", "H")
    hr = om_data["heure_ret"].replace(":", "H")

    # motif : paragraphe justifie (le libelle est souligne)
    label = ["Pour", "accomplir", "la", "mission", "suivante"]
    tokens = [(w, True) for w in label] + [(":", False)] + [(w, False) for w in clean_str(om_data["motif"]).split()]
    sp, avail, LH = wd(" ", "B", 12), 188.6 - LX, 4.87
    lines, cur = [[]], 0.0
    for w, is_lab in tokens:
        ww = wd(w, "B", 12)
        need = ww if not lines[-1] else sp + ww
        if lines[-1] and cur + need > avail:
            lines.append([]); cur, need = 0.0, ww
        lines[-1].append((w, is_lab, ww)); cur += need
    h3 = max(12.3, 2.3 + LH * len(lines) + 0.3)

    heights = [12.2, 12.0, h3, 6.7, 10.0, 10.0, 8.3, 41.2]
    ys = [Y0]
    for h in heights:
        ys.append(ys[-1] + h)
    yb = ys[-1]
    pdf.rect(X0, Y0, X1 - X0, yb - Y0)
    for y in ys[1:-1]:
        pdf.line(X0, y, X1, y)
    pdf.line(78.0, ys[7], 78.0, yb)
    pdf.line(130.9, ys[7], 130.9, yb)

    # ligne 1 : Monsieur/Madame + Matricule
    x = tx(LX, ys[0] + 0.5, "Monsieur/Madame", "BU", 12)
    x = tx(x, ys[0] + 0.5, " ", "B", 12)
    tx(x, ys[0] + 0.5, f": {nom_complet}", "B", 12)
    x = tx(RX, ys[0] + 0.5, "Matricule", "BU", 11)
    tx(x, ys[0] + 0.5, f" : {matricule}", "", 11)

    # ligne 2 : destination
    x = tx(LX, ys[1] + 1.3, "De se rendre à", "BU", 12)
    tx(x, ys[1] + 1.3, f"   : {om_data['destination']}", "B", 12)

    # ligne 3 : motif justifie
    top3 = ys[2] + 2.3
    lab_x0 = lab_x1 = None
    for i, ln in enumerate(lines):
        n = len(ln)
        last = i == len(lines) - 1
        gap = sp if (last or n == 1) else (avail - sum(t[2] for t in ln)) / (n - 1)
        x = LX
        for w, is_lab, ww in ln:
            tx(x, top3 + i * LH, w, "B", 12)
            if is_lab:
                lab_x0 = x if lab_x0 is None else lab_x0
                lab_x1 = x + ww
            x += ww + gap
    if lab_x0 is not None:
        yu = top3 + 0.891 * 12 * K + 0.35
        pdf.line(lab_x0, yu, lab_x1, yu)

    # ligne 4 : conducteur
    x = tx(LX, ys[3] + 2.0, "Conducteur", "BU", 12)
    tx(x, ys[3] + 2.0, " : ", "", 12)
    if om_data["conducteur"]:
        tx(x + wd(" : ", "", 12), ys[3] + 2.0, om_data["conducteur"], "B", 12)
    x = tx(RX, ys[3] + 2.0, "Mle", "BU", 12)
    tx(x, ys[3] + 2.0, " : ", "", 12)
    if om_data["mle_conducteur"]:
        tx(x + wd(" : ", "", 12), ys[3] + 2.0, om_data["mle_conducteur"], "B", 12)

    # lignes 5 et 6 : dates et heures
    x = tx(LX, ys[4] + 1.3, "Date de départ", "BU", 12)
    tx(x, ys[4] + 1.3, f" : {om_data['date_dep']}", "B", 12)
    x = tx(RX, ys[4] + 1.3, "Heure", "BU", 12)
    tx(x, ys[4] + 1.3, f" : {hd}", "B", 12)
    x = tx(LX, ys[5] + 1.3, "Date de retour", "BU", 12)
    tx(x, ys[5] + 1.3, f" : {om_data['date_ret']}", "B", 12)
    x = tx(RX, ys[5] + 2.3, "Heure", "BU", 12)
    tx(x, ys[5] + 1.7, f" : {hr}", "B", 14)

    # ligne 7 : moyen de transport
    x = tx(LX, ys[6] + 1.3, "L'intéressé(e) utilisera", "BU", 12)
    tx(x, ys[6] + 1.3, " : ", "B", 12)

    # ligne 8 : trois colonnes de transport
    t8 = ys[7]

    def case(x, y, w, h, coche):
        pdf.rect(x, y, w, h)
        if coche:
            tb(x + w / 2 - wd("X", "", 10) / 2, y + h / 2 + 1.2, "X", "", 10)

    case(28.0, t8 + 5.5, 9.5, 8.3, transport == "Public")
    tx(40.1, t8 + 7.0, "Transport Public", "I", 12)

    case(78.7, t8 + 4.9, 9.6, 8.6, transport == "Mission")
    tx(93.0, t8 + 7.0, "Voiture de mission", "I", 12)
    x = tx(79.3, t8 + 16.0, "Marque", "BIU", 12)
    x = tx(x, t8 + 16.0, "   : ", "I", 12)
    if transport == "Mission": tx(x, t8 + 16.0, om_data["marque"], "I", 12)
    x = tx(79.3, t8 + 26.0, "N° de plaque", "BIU", 12)
    x = tx(x, t8 + 26.0, " : ", "I", 12)
    if transport == "Mission": tx(x, t8 + 26.0, om_data["plaque"], "I", 12)

    case(134.6, t8 + 2.7, 9.5, 8.9, transport == "Personnelle")
    tx(144.9, t8 + 6.0, "Voiture personnelle", "I", 12)
    x = tx(132.2, t8 + 15.0, "Marque", "IU", 12)
    x = tx(x, t8 + 15.0, " : ", "I", 12)
    if transport == "Personnelle": tx(x, t8 + 15.0, om_data["marque"], "I", 12)
    x = tx(132.2, t8 + 25.0, "Puissance Fiscale   : ", "I", 12)
    if transport == "Personnelle": tx(x, t8 + 25.0, om_data["puissance"], "I", 12)
    x = tx(132.2, t8 + 31.0, "N° de Plaque : ", "I", 12)
    if transport == "Personnelle": tx(x, t8 + 31.0, om_data["plaque"], "I", 12)

    # --- cadre reserve a l'entite de destinations ---
    T2 = yb + 4.2
    r1, r2, r3 = T2 + 9.2, T2 + 19.2, T2 + 44.8
    pdf.set_fill_color(231, 230, 230)
    pdf.rect(X0, T2, X1 - X0, r2 - T2, "F")
    pdf.rect(X0, T2, X1 - X0, r3 - T2)
    pdf.line(X0, r1, X1, r1)
    pdf.line(X0, r2, X1, r2)
    pdf.line(103.8, r1, 103.8, r3)
    tx(105 - wd("Cadre réservé à l'entité de destinations", "", 16) / 2 + 2.5, T2 + 0.5,
       "Cadre réservé à l'entité de destinations", "", 16)
    tx((X0 + 103.8) / 2 - wd("Visa d'arrivée", "", 14) / 2, r1 + 1.0, "Visa d'arrivée", "", 14)
    tx((103.8 + X1) / 2 - wd("Visa de départ", "", 14) / 2, r1 + 1.0, "Visa de départ", "", 14)
    tx(27.0, r2 + 0.4, "Date et Heure d'arrivée :", "", 11)
    tx(27.0, r2 + 9.4, "Cachet et signature :", "", 11)
    tx(105.7, r2 + 0.4, "Date et Heure de départ :", "", 11)
    tx(105.7, r2 + 9.4, "Cachet et signature :", "", 11)

    # --- NB et signatures ---
    x = tx(25.0, r3 + 0.6, "NB", "BU", 10)
    tx(x, r3 + 0.6, " : Le visa de départ est obligatoire pour les missions au-delà d'une journée.", "B", 10)
    tx(25.0, r3 + 9.0, "Le Directeur du Complexe", "B", 14)
    tx(137.4, r3 + 9.0, "Le Directeur Régional", "B", 14)
    return pdf


# ------------------------------------------------------------------
# FENETRE MODIFICATION MOT DE PASSE
# ------------------------------------------------------------------
class ChangePasswordWindow(ctk.CTkToplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Modifier le mot de passe")
        self.geometry("380x300")
        self.resizable(False, False)
        self.grab_set()

        lbl_title = ctk.CTkLabel(self, text="Changer le mot de passe", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_title.pack(pady=20)

        self.entry_old = ctk.CTkEntry(self, placeholder_text="Ancien mot de passe", show="*", width=280, height=35)
        self.entry_old.pack(pady=5)

        self.entry_new = ctk.CTkEntry(self, placeholder_text="Nouveau mot de passe", show="*", width=280, height=35)
        self.entry_new.pack(pady=5)

        self.entry_confirm = ctk.CTkEntry(self, placeholder_text="Confirmer le nouveau mot de passe", show="*", width=280, height=35)
        self.entry_confirm.pack(pady=5)

        btn_save = ctk.CTkButton(self, text="Enregistrer", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, width=280, height=35, command=self.save_new_password)
        btn_save.pack(pady=15)

    def save_new_password(self):
        old_pass = self.entry_old.get().strip()
        new_pass = self.entry_new.get().strip()
        confirm_pass = self.entry_confirm.get().strip()

        current_user, current_password = get_admin_credentials()

        if not _verify_password(old_pass, current_password):
            messagebox.showerror("Erreur", "L'ancien mot de passe est incorrect.")
            return

        if not new_pass:
            messagebox.showerror("Erreur", "Le nouveau mot de passe ne peut pas être vide.")
            return

        if new_pass != confirm_pass:
            messagebox.showerror("Erreur", "Les nouveaux mots de passe ne correspondent pas.")
            return

        save_admin_credentials(current_user, new_pass)
        messagebox.showinfo("Succès", "Mot de passe modifié avec succès !")
        self.destroy()


# ------------------------------------------------------------------
# FENETRE CREATION DE COMPTE
# ------------------------------------------------------------------
class CreateAccountWindow(ctk.CTkToplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Créer un compte")
        self.geometry("380x360")
        self.resizable(False, False)
        self.grab_set()

        lbl_title = ctk.CTkLabel(self, text="Créer un nouveau compte", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_title.pack(pady=20)

        self.entry_user = ctk.CTkEntry(self, placeholder_text="Nom d'utilisateur", width=280, height=35)
        self.entry_user.pack(pady=5)

        self.entry_pass = ctk.CTkEntry(self, placeholder_text="Mot de passe", show="*", width=280, height=35)
        self.entry_pass.pack(pady=5)

        self.entry_confirm = ctk.CTkEntry(self, placeholder_text="Confirmer le mot de passe", show="*", width=280, height=35)
        self.entry_confirm.pack(pady=5)

        self.role_var = ctk.StringVar(value="Utilisateur")
        self.menu_role = ctk.CTkOptionMenu(self, values=["Administrateur", "Utilisateur"], variable=self.role_var, fg_color=MAIN_COLOR, button_color=MAIN_COLOR_HOVER, width=280, height=35)
        self.menu_role.pack(pady=5)

        btn_save = ctk.CTkButton(self, text="Créer le compte", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, width=280, height=35, command=self.save_account)
        btn_save.pack(pady=15)

    def save_account(self):
        username = self.entry_user.get().strip()
        password = self.entry_pass.get().strip()
        confirm = self.entry_confirm.get().strip()
        role = self.role_var.get()

        if not username or not password or not confirm:
            messagebox.showerror("Erreur", "Tous les champs doivent être remplis !", parent=self)
            return

        if password != confirm:
            messagebox.showerror("Erreur", "Les mots de passe ne correspondent pas !", parent=self)
            return

        try:
            with get_db_connection() as conn:
                cursor = conn.cursor()
                cursor.execute("""
                    CREATE TABLE IF NOT EXISTS users (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        username TEXT UNIQUE,
                        password TEXT,
                        role TEXT
                    )
                """)
                hashed = _hash_password(password)
                cursor.execute("INSERT INTO users (username, password, role) VALUES (?, ?, ?)", (username, hashed, role))
                conn.commit()

            messagebox.showinfo("Succès", f"Compte '{username}' créé avec succès !", parent=self)
            self.destroy()
        except sqlite3.IntegrityError:
            messagebox.showerror("Erreur", "Ce nom d'utilisateur existe déjà.", parent=self)
        except Exception as e:
            messagebox.showerror("Erreur", f"Une erreur est survenue : {e}", parent=self)


# ------------------------------------------------------------------
# FENETRE PARAMETRES (CONNEXION / DECONNEXION & THEME)
# ------------------------------------------------------------------
class SettingsWindow(ctk.CTkToplevel):
    def __init__(self, parent, on_logout_callback):
        super().__init__(parent)
        self.title("Paramètres")
        self.geometry("400x470")
        self.resizable(False, False)
        self.grab_set()

        self.on_logout_callback = on_logout_callback

        lbl_title = ctk.CTkLabel(self, text="Paramètres de l'application", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_title.pack(pady=20)

        # Gestion du thème
        lbl_theme = ctk.CTkLabel(self, text="Apparence du thème :", font=ctk.CTkFont(weight="bold"))
        lbl_theme.pack(anchor="w", padx=30, pady=(5, 5))

        self.theme_menu = ctk.CTkOptionMenu(
            self, 
            values=["System", "Light", "Dark"], 
            fg_color=MAIN_COLOR, 
            button_color=MAIN_COLOR_HOVER, 
            command=ctk.set_appearance_mode
        )
        self.theme_menu.set(ctk.get_appearance_mode())
        self.theme_menu.pack(fill="x", padx=30, pady=5)

        # Sécurité (Mot de passe & Création de compte)
        lbl_pwd = ctk.CTkLabel(self, text="Sécurité & Comptes :", font=ctk.CTkFont(weight="bold"))
        lbl_pwd.pack(anchor="w", padx=30, pady=(15, 5))

        btn_pwd = ctk.CTkButton(
            self, 
            text="Modifier le mot de passe", 
            fg_color=MAIN_COLOR, 
            hover_color=MAIN_COLOR_HOVER, corner_radius=8, 
            command=lambda: ChangePasswordWindow(self)
        )
        btn_pwd.pack(fill="x", padx=30, pady=5)

        btn_create_acc = ctk.CTkButton(
            self, 
            text="Créer un nouveau compte", 
            fg_color=MAIN_COLOR, 
            hover_color=MAIN_COLOR_HOVER, corner_radius=8, 
            command=lambda: CreateAccountWindow(self)
        )
        btn_create_acc.pack(fill="x", padx=30, pady=5)

        btn_etab = ctk.CTkButton(
            self,
            text="Données de l'établissement",
            fg_color=MAIN_COLOR,
            hover_color=MAIN_COLOR_HOVER, corner_radius=8,
            command=lambda: EtabWindow(self)
        )
        btn_etab.pack(fill="x", padx=30, pady=5)

        # Bouton Connexion / Déconnexion
        lbl_session = ctk.CTkLabel(self, text="Gestion de la session :", font=ctk.CTkFont(weight="bold"))
        lbl_session.pack(anchor="w", padx=30, pady=(15, 5))

        btn_logout = ctk.CTkButton(
            self, 
            text="Déconnexion (Verrouiller)", 
            fg_color="#a83232", 
            hover_color="#7e2424", 
            command=self.trigger_logout
        )
        btn_logout.pack(fill="x", padx=30, pady=5)

    def trigger_logout(self):
        self.destroy()
        self.on_logout_callback()


class EtabWindow(ctk.CTkToplevel):
    """Donnees de l'etablissement utilisees dans les PDF (en-tetes, pieds de page, references)."""
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Données de l'établissement")
        self.geometry("520x580")
        self.resizable(False, False)
        self.grab_set()
        ctk.CTkLabel(self, text="Données de l'établissement", font=ctk.CTkFont(size=16, weight="bold")).pack(pady=(16, 2))
        ctk.CTkLabel(self, text="Ces textes apparaissent dans les attestations et les ordres de mission.",
                     text_color="gray").pack(pady=(0, 10))
        cur = get_etab()
        self.ent = {}
        for key, label in ETAB_LABELS:
            ctk.CTkLabel(self, text=label, anchor="w").pack(fill="x", padx=30)
            e = ctk.CTkEntry(self)
            e.pack(fill="x", padx=30, pady=(0, 6))
            e.insert(0, cur[key])
            self.ent[key] = e
        bar = ctk.CTkFrame(self, fg_color="transparent")
        bar.pack(pady=12)
        ctk.CTkButton(bar, text="Enregistrer", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, command=self.save).pack(side="left", padx=6)
        ctk.CTkButton(bar, text="Valeurs d'origine", fg_color="gray", command=self.reset).pack(side="left", padx=6)

    def save(self):
        try:
            save_etab({k: e.get() for k, e in self.ent.items()})
        except OSError as ex:
            logger.exception("Enregistrement des donnees de l'etablissement impossible")
            messagebox.showerror("Établissement", f"Impossible d'enregistrer :\n{ex}", parent=self)
            return
        messagebox.showinfo("Établissement", "Enregistré. Les prochains documents utiliseront ces données.", parent=self)
        self.destroy()

    def reset(self):
        for k, e in self.ent.items():
            e.delete(0, "end")
            e.insert(0, ETAB_DEFAULTS[k])


# ------------------------------------------------------------------
# PAGE D\'ACCUEIL (SPLASH SCREEN)
# ------------------------------------------------------------------
class SplashScreen(tk.Toplevel):
    """Page d\'accueil professionnelle affichee au demarrage du logiciel."""

    BG         = "#0d2c54"
    ACCENT     = "#e8a020"
    TEXT_LIGHT = "#ffffff"
    TEXT_GREY  = "#b0c4de"
    BAR_BG     = "#1a3a6b"
    BAR_FG     = "#e8a020"
    WIDTH      = 700
    HEIGHT     = 420
    DURATION   = 3500

    def __init__(self, root, on_done_callback):
        super().__init__(root)
        self.on_done = on_done_callback
        self.overrideredirect(True)
        self.attributes("-topmost", True)

        sw = self.winfo_screenwidth()
        sh = self.winfo_screenheight()
        x  = (sw - self.WIDTH)  // 2
        y  = (sh - self.HEIGHT) // 2
        self.geometry(f"{self.WIDTH}x{self.HEIGHT}+{x}+{y}")

        self.canvas = tk.Canvas(self, width=self.WIDTH, height=self.HEIGHT,
                                bg=self.BG, highlightthickness=0)
        self.canvas.pack()

        self._draw_background()
        self._draw_logo_zone()
        self._draw_texts()
        self._draw_progress_bar()
        self._draw_footer()

        self._progress = 0
        self._animate_bar()
        self.after(self.DURATION, self._finish)

    def _draw_background(self):
        c = self.canvas
        c.create_rectangle(0, 0, 8, self.HEIGHT, fill=self.ACCENT, outline="")
        c.create_rectangle(12, 0, 16, self.HEIGHT, fill="#c07010", outline="")
        c.create_line(0, 72, self.WIDTH, 72, fill=self.ACCENT, width=1)
        c.create_line(0, self.HEIGHT - 60, self.WIDTH, self.HEIGHT - 60,
                      fill="#1a3a6b", width=1)

    def _draw_logo_zone(self):
        c = self.canvas
        c.create_oval(28, 14, 84, 58, fill="#1a3a6b", outline=self.ACCENT, width=2)
        logo_png = os.path.join(BASE_DIR, "logo_ofppt.png")
        logo_jpg = os.path.join(BASE_DIR, "logo_ofppt.jpg")
        self._logo_img = None
        try:
            from PIL import Image, ImageTk
            src = logo_png if os.path.exists(logo_png) else (logo_jpg if os.path.exists(logo_jpg) else None)
            if src:
                img = Image.open(src).convert("RGBA").resize((46, 34), Image.LANCZOS)
                self._logo_img = ImageTk.PhotoImage(img)
                c.create_image(56, 36, image=self._logo_img)
            else:
                raise FileNotFoundError
        except Exception:
            c.create_text(56, 36, text="OFPPT", fill=self.ACCENT,
                          font=("Arial", 11, "bold"))

    def _draw_texts(self):
        c = self.canvas
        c.create_text(self.WIDTH // 2 + 20, 36,
                      text="COMPLEXE DE FORMATION PROFESSIONNELLE BERKANE",
                      fill=self.TEXT_GREY, font=("Arial", 9), anchor="center")
        c.create_text(self.WIDTH // 2, 130,
                      text="GESTION DU PERSONNEL",
                      fill=self.TEXT_LIGHT, font=("Arial", 28, "bold"), anchor="center")
        c.create_text(self.WIDTH // 2, 170,
                      text="Systeme Integre de Gestion RH",
                      fill=self.ACCENT, font=("Arial", 13, "italic"), anchor="center")
        pad = 120
        c.create_line(pad, 196, self.WIDTH - pad, 196, fill="#1a3a6b", width=1)
        features = [
            "Personnel & Absences",
            "Ordres de Mission",
            "Emploi du Temps",
            "Formations",
        ]
        cols = [130, 390]
        for i, feat in enumerate(features):
            x = cols[i % 2]
            y = 218 + (i // 2) * 24
            c.create_text(x, y, text=f">>  {feat}", fill=self.TEXT_GREY,
                          font=("Arial", 10), anchor="w")
        self._loading_txt = c.create_text(self.WIDTH // 2, self.HEIGHT - 70,
                                          text="Chargement en cours...",
                                          fill=self.TEXT_GREY,
                                          font=("Arial", 9, "italic"),
                                          anchor="center")

    def _draw_progress_bar(self):
        c = self.canvas
        bx, by = 60, self.HEIGHT - 50
        bw, bh = self.WIDTH - 120, 10
        r = 5
        c.create_arc(bx, by, bx+2*r, by+bh, start=90, extent=180, fill=self.BAR_BG, outline="")
        c.create_arc(bx+bw-2*r, by, bx+bw, by+bh, start=270, extent=180, fill=self.BAR_BG, outline="")
        c.create_rectangle(bx+r, by, bx+bw-r, by+bh, fill=self.BAR_BG, outline="")
        self._bar_x  = bx; self._bar_y = by
        self._bar_w  = bw; self._bar_h = bh; self._bar_r = r
        self._bar_fill = None

    def _draw_footer(self):
        c = self.canvas
        c.create_text(self.WIDTH // 2, self.HEIGHT - 20,
                      text="(c) 2025  OFPPT - CF Berkane  |  Tous droits reserves",
                      fill="#4a6a8a", font=("Arial", 8), anchor="center")
        c.create_text(self.WIDTH - 20, self.HEIGHT - 20,
                      text="v 1.0", fill="#4a6a8a", font=("Arial", 8), anchor="e")

    def _animate_bar(self):
        if not self.winfo_exists():
            return
        c  = self.canvas
        bx = self._bar_x; by = self._bar_y
        bw = self._bar_w; bh = self._bar_h; r = self._bar_r

        self._progress = min(self._progress + 1.8, 100)
        fw = int(bw * self._progress / 100)

        if self._bar_fill:
            for item in self._bar_fill:
                c.delete(item)
        self._bar_fill = []

        if fw > 2 * r:
            self._bar_fill.append(c.create_arc(bx, by, bx+2*r, by+bh,
                                               start=90, extent=180, fill=self.BAR_FG, outline=""))
            self._bar_fill.append(c.create_arc(bx+fw-2*r, by, bx+fw, by+bh,
                                               start=270, extent=180, fill=self.BAR_FG, outline=""))
            self._bar_fill.append(c.create_rectangle(bx+r, by, bx+fw-r, by+bh,
                                                     fill=self.BAR_FG, outline=""))
            self._bar_fill.append(c.create_rectangle(bx+r, by+1, bx+fw-r, by+3,
                                                     fill="#f5c842", outline=""))

        steps = [
            (0,  "Initialisation..."),
            (25, "Chargement de la base de donnees..."),
            (55, "Preparation de l\'interface..."),
            (80, "Verification des permissions..."),
            (95, "Presque pret..."),
        ]
        msg = "Chargement en cours..."
        for threshold, text in reversed(steps):
            if self._progress >= threshold:
                msg = text
                break
        c.itemconfig(self._loading_txt, text=msg)

        if self._progress < 100:
            self.after(30, self._animate_bar)

    def _finish(self):
        self.destroy()
        self.on_done()


# ------------------------------------------------------------------
# FENETRE DE LOGIN (AUTHENTIFICATION)
# ------------------------------------------------------------------
class LoginWindow(ctk.CTk):
    def __init__(self, on_login_success):
        super().__init__()
        self.title("OFPPT - Connexion")
        self.geometry("400x350")
        self.resizable(False, False)
        self.on_login_success = on_login_success

        self.eval('tk::PlaceWindow . center')

        lbl_title = ctk.CTkLabel(self, text="CONNEXION", font=ctk.CTkFont(size=20, weight="bold"), text_color=MAIN_COLOR)
        lbl_title.pack(pady=(30, 20))
        ctk.CTkLabel(self, text="Utilisateur : administrateur (pré-rempli)",
                     font=ctk.CTkFont(size=11), text_color="#6b7a89").pack()

        # Nom d'utilisateur deja saisi (administrateur) : plus que le mot de passe a taper
        stored_user, _stored_hash = get_admin_credentials()
        self.entry_user = ctk.CTkEntry(self, width=280, height=40, justify="center",
                                       font=ctk.CTkFont(size=14, weight="bold"))
        self.entry_user.insert(0, stored_user)
        self.entry_user.configure(state="disabled")
        self.entry_user.pack(pady=10)

        self.entry_pass = ctk.CTkEntry(self, placeholder_text="Mot de passe", show="*", width=280, height=40,
                                       justify="center")
        self.entry_pass.pack(pady=10)
        self.entry_pass.bind("<Return>", lambda event: self.verify_login())
        self.entry_pass.focus()

        btn_login = ctk.CTkButton(self, text="Se connecter", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, width=280, height=40, command=self.verify_login)
        btn_login.pack(pady=20)

    def verify_login(self):
        attente = login_wait_seconds()
        if attente:
            messagebox.showwarning("Trop de tentatives", f"Trop d'échecs de connexion.\nRéessayez dans {attente} seconde(s).")
            return
        username = self.entry_user.get().strip()
        password = self.entry_pass.get()
        essais = [password] if password == password.strip() else [password, password.strip()]

        ok = False
        stored_user, stored_pass = get_admin_credentials()
        if username == stored_user:
            bon = next((p for p in essais if _verify_password(p, stored_pass)), None)
            if bon is not None:
                ok = True
                if password_needs_upgrade(stored_pass):          # ancien hash SHA-256 -> PBKDF2
                    try:
                        save_admin_credentials(stored_user, bon)
                    except Exception:
                        logger.exception("Mise a niveau du mot de passe administrateur impossible")
                try:
                    if os.path.exists(INITIAL_PASSWORD_FILE):
                        os.remove(INITIAL_PASSWORD_FILE)
                except OSError:
                    logger.warning("Impossible de supprimer le mot de passe initial")

        if not ok:
            try:
                with get_db_connection() as conn:
                    row = conn.execute("SELECT password FROM users WHERE username=?", (username,)).fetchone()
                    bon = next((p for p in essais if row and _verify_password(p, row[0])), None)
                    if bon is not None:
                        ok = True
                        if password_needs_upgrade(row[0]):
                            conn.execute("UPDATE users SET password=? WHERE username=?", (_hash_password(bon), username))
            except Exception:
                logger.exception("Erreur de base de donnees pendant la connexion")
                messagebox.showerror("Erreur", "Impossible de lire la base de données.\nConsultez le fichier application.log.")
                return

        if ok:                          # la connexion a la base est deja fermee : l'application peut demarrer
            login_succeeded()
            self.destroy()
            self.on_login_success()
            return
        login_failed()
        messagebox.showerror("Erreur d'authentification", "Nom d'utilisateur ou mot de passe incorrect.")


# ------------------------------------------------------------------
# FENETRE LISTE DES ABSENCES (POP-UP CLIC)
# ------------------------------------------------------------------
class AbsencesListWindow(ctk.CTkToplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Liste des Absences Enregistrées")
        self.geometry("600x450")
        self.resizable(False, False)
        self.grab_set()

        lbl_title = ctk.CTkLabel(self, text="Détails de toutes les absences", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_title.pack(pady=15)

        scroll_frame = ctk.CTkScrollableFrame(self)
        scroll_frame.pack(fill="both", expand=True, padx=20, pady=(0, 20))

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute('''
                SELECT p.nom, p.prenom, a.motif, a.date_debut, a.date_fin 
                FROM absences a 
                JOIN personnel p ON a.personnel_id = p.id 
                ORDER BY a.id DESC
            ''')
            rows = cursor.fetchall()

        if not rows:
            ctk.CTkLabel(scroll_frame, text="Aucune absence enregistrée pour le moment.", font=ctk.CTkFont(slant="italic")).pack(pady=30)
            return

        for row in rows:
            nom, prenom, motif, d_deb, d_fin = row
            card = ctk.CTkFrame(scroll_frame)
            card.pack(fill="x", pady=5, padx=5)

            txt_date = f"Du {d_deb} au {d_fin}" if (absence_multi(motif) and d_deb != d_fin) else f"Le {d_deb}"
            info = f"• {nom.upper()} {prenom}  |  Motif : {motif}  |  {txt_date}"
            
            lbl_item = ctk.CTkLabel(card, text=info, font=ctk.CTkFont(size=12, weight="bold"), anchor="w")
            lbl_item.pack(fill="x", padx=15, pady=12)


# ------------------------------------------------------------------
# FENETRE LISTE DU PERSONNEL (POP-UP CLIC)
# ------------------------------------------------------------------
class PersonnelListWindow(ctk.CTkToplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Liste de tout le Personnel")
        self.geometry("650x450")
        self.resizable(False, False)
        self.grab_set()

        lbl_title = ctk.CTkLabel(self, text="Répertoire complet du Personnel", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_title.pack(pady=15)

        scroll_frame = ctk.CTkScrollableFrame(self)
        scroll_frame.pack(fill="both", expand=True, padx=20, pady=(0, 20))

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute('SELECT nom, prenom, cin, specialite, fonction FROM personnel ORDER BY nom ASC')
            rows = cursor.fetchall()

        if not rows:
            ctk.CTkLabel(scroll_frame, text="Aucun agent enregistré dans le personnel.", font=ctk.CTkFont(slant="italic")).pack(pady=30)
            return

        for row in rows:
            nom, prenom, cin, spec, fn = row
            card = ctk.CTkFrame(scroll_frame)
            card.pack(fill="x", pady=5, padx=5)

            info = f"• {nom.upper()} {prenom}  |  CIN : {cin or 'N/A'}  |  Poste : {spec or 'N/A'}"
            lbl_item = ctk.CTkLabel(card, text=info, font=ctk.CTkFont(size=12, weight="bold"), anchor="w")
            lbl_item.pack(fill="x", padx=15, pady=12)


# ------------------------------------------------------------------
# FENETRE LISTE DES FORMATIONS (POP-UP CLIC)
# ------------------------------------------------------------------
class FormationsListWindow(ctk.CTkToplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Liste des Formations Planifiées")
        self.geometry("650x450")
        self.resizable(False, False)
        self.grab_set()

        lbl_title = ctk.CTkLabel(self, text="Détails de toutes les formations planifiées", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_title.pack(pady=15)

        scroll_frame = ctk.CTkScrollableFrame(self)
        scroll_frame.pack(fill="both", expand=True, padx=20, pady=(0, 20))

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute('''
                SELECT p.nom, p.prenom, f.theme, f.lieu, f.date_debut, f.date_fin 
                FROM formations f 
                JOIN personnel p ON f.personnel_id = p.id 
                ORDER BY f.id DESC
            ''')
            rows = cursor.fetchall()

        if not rows:
            ctk.CTkLabel(scroll_frame, text="Aucune formation planifiée pour le moment.", font=ctk.CTkFont(slant="italic")).pack(pady=30)
            return

        for row in rows:
            nom, prenom, theme, lieu, d_deb, d_fin = row
            card = ctk.CTkFrame(scroll_frame)
            card.pack(fill="x", pady=5, padx=5)

            info = f"• {nom.upper()} {prenom} | Thème : {theme} | Lieu : {lieu} | Du {d_deb} au {d_fin}"
            lbl_item = ctk.CTkLabel(card, text=info, font=ctk.CTkFont(size=12, weight="bold"), anchor="w")
            lbl_item.pack(fill="x", padx=15, pady=12)


# ------------------------------------------------------------------
# FENETRE D'APERCU : FORMATIONS TROUVEES DANS LE PDF / EXCEL
# ------------------------------------------------------------------
class ImportFormationsWindow(ctk.CTkToplevel):
    def __init__(self, app, matches, stats, filename):
        super().__init__(app)
        self.app = app
        self.title("Importer des formations")
        self.geometry("980x600")
        self.grab_set()

        # formations deja enregistrees (evite les doublons)
        with get_db_connection() as conn:
            cur = conn.cursor()
            cur.execute("SELECT personnel_id, theme, date_debut, date_fin FROM formations")
            existing = {(r[0], _fnorm(r[1]), r[2], r[3]) for r in cur.fetchall()}

        ctk.CTkLabel(self, text=f"Formations trouvées dans « {os.path.basename(filename)} »",
                     font=ctk.CTkFont(size=16, weight="bold")).pack(pady=(15, 2))
        resume = (f"{len(matches)} formation(s) vous concernent — "
                  f"{stats['ignorees']} ligne(s) d'autres personnes ignorée(s)")
        if stats["sans_date"]:
            resume += f" — {stats['sans_date']} ligne(s) à votre nom sans date (ignorée(s))"
        ctk.CTkLabel(self, text=resume, font=ctk.CTkFont(size=12)).pack(pady=(0, 8))

        scroll = ctk.CTkScrollableFrame(self)
        scroll.pack(fill="both", expand=True, padx=20, pady=(0, 10))

        self.items = []
        for m in matches:
            d1, d2 = m["d_debut"].strftime("%d/%m/%Y"), m["d_fin"].strftime("%d/%m/%Y")
            deja = (m["p_id"], _fnorm(m["theme"]), d1, d2) in existing
            var = ctk.BooleanVar(value=not deja)
            txt = f"{m['p_name']} | {m['theme']} | {m['lieu']} | Du {d1} au {d2}"
            m["om"] = not (("teams" in _fnorm(m["lieu"])) or ("distance" in _fnorm(m["theme"])))
            if deja:
                txt += "   (déjà enregistrée)"
            elif not m["om"]:
                txt += "   (à distance : sans ordre de mission)"
            ctk.CTkCheckBox(scroll, text=txt, variable=var, font=ctk.CTkFont(size=12)).pack(anchor="w", padx=8, pady=4)
            self.items.append((var, m))

        if not matches:
            ctk.CTkLabel(scroll, text="Aucune formation ne concerne le personnel enregistré.",
                         font=ctk.CTkFont(slant="italic")).pack(pady=30)

        bar = ctk.CTkFrame(self, fg_color="transparent")
        bar.pack(fill="x", padx=20, pady=(0, 15))
        ctk.CTkButton(bar, text="Annuler", fg_color="gray", width=100, command=self.destroy).pack(side="right", padx=5)
        if matches:
            ctk.CTkButton(bar, text="Importer la sélection", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER,
                          command=self._import).pack(side="right", padx=5)

    def _import(self):
        chosen = [m for var, m in self.items if var.get()]
        if not chosen:
            messagebox.showwarning("Import", "Aucune formation sélectionnée.", parent=self)
            return
        with get_db_connection() as conn:
            cur = conn.cursor()
            for m in chosen:
                self.app._enregistrer_formation(cur, m["p_id"], m["p_name"], m["theme"], m["lieu"],
                                                m["d_debut"], m["d_fin"], avec_om=m.get("om", True))
            conn.commit()
        messagebox.showinfo("Import", f"{len(chosen)} formation(s) importée(s).\n\n"
                                      "Les ordres de mission correspondants ont été ajoutés "
                                      "(sauf pour les formations à distance).", parent=self)
        self.destroy()
        try:
            self.app.load_formations_list()
        except Exception:
            logger.exception("Rafraichissement de la liste des formations impossible")


# ------------------------------------------------------------------
# FENETRE DE SAISIE POUR ORDRE DE MISSION
# ------------------------------------------------------------------
class OrdreMissionDialog(ctk.CTkToplevel):
    def __init__(self, parent, personnel_info, on_generate_callback, initial_data=None):
        super().__init__(parent)
        self.title("Ordre de Mission - Saisie")
        self.geometry("520x720")
        self.resizable(False, False)
        self.grab_set()

        self.personnel_info = personnel_info
        self.on_generate_callback = on_generate_callback
        self.om_id = (initial_data or {}).get("om_id")

        nom_complet = f"{personnel_info[1].upper()} {personnel_info[2]}"

        label = ctk.CTkLabel(self, text=f"Ordre de Mission\n{nom_complet}", font=ctk.CTkFont(size=16, weight="bold"))
        label.pack(pady=10)

        scroll = ctk.CTkScrollableFrame(self, height=560)
        scroll.pack(fill="both", expand=True, padx=15, pady=5)

        self.entry_num = ctk.CTkEntry(scroll, placeholder_text="N° Ordre de Mission (ex: 12)")
        self.entry_num.pack(fill="x", pady=5)

        self.entry_destination = ctk.CTkEntry(scroll, placeholder_text="De se rendre à (Destination)")
        self.entry_destination.pack(fill="x", pady=5)

        self.entry_motif = ctk.CTkEntry(scroll, placeholder_text="Pour accomplir la mission suivante")
        self.entry_motif.pack(fill="x", pady=5)

        self.entry_conducteur = ctk.CTkEntry(scroll, placeholder_text="Conducteur (Optionnel)")
        self.entry_conducteur.pack(fill="x", pady=5)

        self.entry_mle_conducteur = ctk.CTkEntry(scroll, placeholder_text="Mle Conducteur (Optionnel)")
        self.entry_mle_conducteur.pack(fill="x", pady=5)

        heures_list = [f"{h:02d}:{m:02d}" for h in range(6, 22) for m in (0, 30) if not (h == 21 and m == 30)]

        frame_dep_label = ctk.CTkLabel(scroll, text="Départ :", font=ctk.CTkFont(weight="bold"))
        frame_dep_label.pack(anchor="w", pady=(5, 0))

        frame_dep = ctk.CTkFrame(scroll, fg_color="transparent")
        frame_dep.pack(fill="x", pady=2)

        self.cal_dep = DateEntry(frame_dep, date_pattern='dd/mm/yyyy', width=12, background=MAIN_COLOR, foreground='white', borderwidth=2)
        self.cal_dep.pack(side="left", padx=5, pady=5)

        self.combo_heure_dep = ctk.CTkOptionMenu(frame_dep, values=heures_list, fg_color=MAIN_COLOR, button_color=MAIN_COLOR_HOVER)
        self.combo_heure_dep.set("08:00")
        self.combo_heure_dep.pack(side="right", expand=True, fill="x", padx=5)

        frame_ret_label = ctk.CTkLabel(scroll, text="Retour :", font=ctk.CTkFont(weight="bold"))
        frame_ret_label.pack(anchor="w", pady=(5, 0))

        frame_ret = ctk.CTkFrame(scroll, fg_color="transparent")
        frame_ret.pack(fill="x", pady=2)

        self.cal_ret = DateEntry(frame_ret, date_pattern='dd/mm/yyyy', width=12, background=MAIN_COLOR, foreground='white', borderwidth=2)
        self.cal_ret.pack(side="left", padx=5, pady=5)

        self.combo_heure_ret = ctk.CTkOptionMenu(frame_ret, values=heures_list, fg_color=MAIN_COLOR, button_color=MAIN_COLOR_HOVER)
        self.combo_heure_ret.set("18:00")
        self.combo_heure_ret.pack(side="right", expand=True, fill="x", padx=5)

        lbl_tr = ctk.CTkLabel(scroll, text="Moyen de transport :", font=ctk.CTkFont(weight="bold"))
        lbl_tr.pack(anchor="w", pady=(10, 2))

        self.transport_type = ctk.StringVar(value="Public")

        rb1 = ctk.CTkRadioButton(scroll, text="Transport Public", variable=self.transport_type, value="Public", fg_color=MAIN_COLOR)
        rb1.pack(anchor="w", pady=2)

        rb2 = ctk.CTkRadioButton(scroll, text="Voiture de mission", variable=self.transport_type, value="Mission", fg_color=MAIN_COLOR)
        rb2.pack(anchor="w", pady=2)

        rb3 = ctk.CTkRadioButton(scroll, text="Voiture personnelle", variable=self.transport_type, value="Personnelle", fg_color=MAIN_COLOR)
        rb3.pack(anchor="w", pady=2)

        self.entry_marque = ctk.CTkEntry(scroll, placeholder_text="Marque du véhicule")
        self.entry_marque.pack(fill="x", pady=4)

        self.entry_plaque = ctk.CTkEntry(scroll, placeholder_text="N° de plaque")
        self.entry_plaque.pack(fill="x", pady=4)

        self.entry_puissance = ctk.CTkEntry(scroll, placeholder_text="Puissance Fiscale (pour voiture personnelle)")
        self.entry_puissance.pack(fill="x", pady=4)

        if initial_data:
            if initial_data.get("num"):
                self.entry_num.insert(0, initial_data["num"])
            if initial_data.get("transport_type"):
                self.transport_type.set(initial_data["transport_type"])
            for key, widget in (("marque", self.entry_marque), ("plaque", self.entry_plaque), ("puissance", self.entry_puissance),
                                ("conducteur", self.entry_conducteur), ("mle_conducteur", self.entry_mle_conducteur)):
                if initial_data.get(key):
                    widget.insert(0, initial_data[key])
            if initial_data.get("destination"):
                self.entry_destination.insert(0, initial_data["destination"])
            if initial_data.get("motif"):
                self.entry_motif.insert(0, initial_data["motif"])
            if initial_data.get("date_dep"):
                try:
                    dt_d = datetime.strptime(initial_data["date_dep"], "%d/%m/%Y")
                    self.cal_dep.set_date(dt_d)
                except Exception:
                    logger.debug("Date de depart illisible : %r", initial_data.get("date_dep"))
            if initial_data.get("heure_dep"):
                self.combo_heure_dep.set(initial_data["heure_dep"])
            if initial_data.get("date_ret"):
                try:
                    dt_r = datetime.strptime(initial_data["date_ret"], "%d/%m/%Y")
                    self.cal_ret.set_date(dt_r)
                except Exception:
                    logger.debug("Date de retour illisible : %r", initial_data.get("date_ret"))
            if initial_data.get("heure_ret"):
                self.combo_heure_ret.set(initial_data["heure_ret"])

        btn_gen = ctk.CTkButton(self, text="Afficher Ordre de Mission (PDF)", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.generate)
        btn_gen.pack(pady=10)

    def generate(self):
        try:
            data = {
                "num": self.entry_num.get().strip() or "____",
                "destination": self.entry_destination.get().strip(),
                "motif": self.entry_motif.get().strip(),
                "conducteur": self.entry_conducteur.get().strip(),
                "mle_conducteur": self.entry_mle_conducteur.get().strip(),
                "date_dep": self.cal_dep.get_date().strftime("%d/%m/%Y"),
                "heure_dep": self.combo_heure_dep.get(),
                "date_ret": self.cal_ret.get_date().strftime("%d/%m/%Y"),
                "heure_ret": self.combo_heure_ret.get(),
                "transport_type": self.transport_type.get(),
                "marque": self.entry_marque.get().strip(),
                "plaque": self.entry_plaque.get().strip(),
                "puissance": self.entry_puissance.get().strip(),
                "om_id": self.om_id,
            }

            if not data["destination"] or not data["motif"]:
                messagebox.showerror("Erreur", "La destination et le motif sont obligatoires.")
                return

            self.on_generate_callback(self.personnel_info, data)
            self.destroy()
        except Exception as e:
            messagebox.showerror("Erreur", f"Une erreur est survenue lors de la saisie : {str(e)}")


# ------------------------------------------------------------------
# FENETRE DE MODIFICATION D'UN MEMBRE DU PERSONNEL
# ------------------------------------------------------------------
class EditPersonnelWindow(ctk.CTkToplevel):
    def __init__(self, parent, personnel_data, on_save_callback):
        super().__init__(parent)
        self.title("Modifier Personnel")
        self.geometry("520x700")
        self.resizable(False, False)
        self.grab_set()

        self.personnel_id = personnel_data[0]
        self.on_save_callback = on_save_callback

        with get_db_connection() as conn:
            _c = conn.cursor()
            _c.execute("SELECT salaire, masse_statutaire FROM personnel WHERE id=?", (self.personnel_id,))
            _r = _c.fetchone()
        self._sal_db = (_r[0] if _r and _r[0] not in (None, "") else "")
        try:
            self._ms_db = ("%g" % float(_r[1])) if _r and _r[1] not in (None, "", 0) else ""
        except (TypeError, ValueError):
            self._ms_db = ""

        label = ctk.CTkLabel(self, text="Modifier les Informations", font=ctk.CTkFont(size=18, weight="bold"))
        label.pack(pady=15)

        self.entries = {}
        fields = [
            ("Nom", personnel_data[1]),
            ("Prénom", personnel_data[2]),
            ("CIN / Matricule", personnel_data[3]),
            ("Spécialité / Poste", personnel_data[4]),
            ("Fonction", personnel_data[5]),
            ("Grade", personnel_data[6]),
            ("Lieu d'affectation", personnel_data[7]),
            ("Salaire de base (DH)", self._sal_db),
            ("Masse statutaire (h/semaine)", self._ms_db)
        ]

        for field_name, value in fields:
            frame = ctk.CTkFrame(self, fg_color="transparent")
            frame.pack(fill="x", padx=25, pady=4)

            lbl = ctk.CTkLabel(frame, text=field_name, width=190, anchor="w")
            lbl.pack(side="left")

            entry = ctk.CTkEntry(frame)
            val_str = str(value) if value is not None and str(value) != 'nan' else ""
            entry.insert(0, val_str)
            entry.pack(side="right", expand=True, fill="x")
            self.entries[field_name] = entry

        btn_save = ctk.CTkButton(self, text="Enregistrer les modifications", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.save)
        btn_save.pack(pady=20)

    def save(self):
        nom = self.entries["Nom"].get().strip()
        prenom = self.entries["Prénom"].get().strip()
        cin = self.entries["CIN / Matricule"].get().strip()
        spec = self.entries["Spécialité / Poste"].get().strip()
        fn = self.entries["Fonction"].get().strip()
        grd = self.entries["Grade"].get().strip()
        lieu = self.entries["Lieu d'affectation"].get().strip()

        if not nom or not prenom:
            messagebox.showerror("Erreur", "Le nom et le prénom sont obligatoires.")
            return

        sal_txt = self.entries["Salaire de base (DH)"].get().strip().replace(",", ".")
        try:
            salaire = float(sal_txt) if sal_txt else 0.0
        except ValueError:
            messagebox.showerror("Erreur", "Le salaire doit être un nombre.")
            return

        ms_txt = self.entries["Masse statutaire (h/semaine)"].get().strip().replace(",", ".")
        try:
            masse = float(ms_txt) if ms_txt else None
            if masse is not None and not 0 <= masse <= 80:
                raise ValueError
        except ValueError:
            messagebox.showerror("Erreur", "La masse statutaire doit être un nombre d'heures par semaine (ex. 26).")
            return

        with get_db_connection() as conn:
            cursor = conn.cursor()
            try:
                cursor.execute('''
                    UPDATE personnel 
                    SET nom=?, prenom=?, cin=?, specialite=?, fonction=?, echelle=?, categorie=?, salaire=?, masse_statutaire=?
                    WHERE id=?
                ''', (nom, prenom, cin, spec, fn, grd, lieu, salaire, masse, self.personnel_id))
                conn.commit()
                messagebox.showinfo("Succès", "Informations mises à jour avec succès !")
                self.on_save_callback()
                self.destroy()
            except sqlite3.IntegrityError:
                messagebox.showerror("Erreur", "Le CIN/Matricule existe déjà pour un autre agent.")


# ------------------------------------------------------------------
# FENETRE D'AJOUT D'UN MEMBRE DU PERSONNEL
# ------------------------------------------------------------------
class AddPersonnelWindow(ctk.CTkToplevel):
    def __init__(self, parent, on_save_callback):
        super().__init__(parent)
        self.title("Ajouter un agent")
        self.geometry("520x700")
        self.resizable(False, False)
        self.grab_set()

        self.on_save_callback = on_save_callback

        label = ctk.CTkLabel(self, text="Nouveau Membre du Personnel", font=ctk.CTkFont(size=18, weight="bold"))
        label.pack(pady=15)

        self.entries = {}
        fields = [
            "Nom",
            "Prénom",
            "CIN / Matricule",
            "Spécialité / Poste",
            "Fonction",
            "Grade",
            "Lieu d'affectation",
            "Salaire de base (DH)",
            "Masse statutaire (h/semaine)"
        ]

        for field_name in fields:
            frame = ctk.CTkFrame(self, fg_color="transparent")
            frame.pack(fill="x", padx=25, pady=4)

            lbl = ctk.CTkLabel(frame, text=field_name, width=190, anchor="w")
            lbl.pack(side="left")

            entry = ctk.CTkEntry(frame)
            entry.pack(side="right", expand=True, fill="x")
            self.entries[field_name] = entry

        btn_save = ctk.CTkButton(self, text="Ajouter", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.save)
        btn_save.pack(pady=20)

    def save(self):
        nom = self.entries["Nom"].get().strip()
        prenom = self.entries["Prénom"].get().strip()
        cin = self.entries["CIN / Matricule"].get().strip()
        spec = self.entries["Spécialité / Poste"].get().strip()
        fn = self.entries["Fonction"].get().strip()
        grd = self.entries["Grade"].get().strip()
        lieu = self.entries["Lieu d'affectation"].get().strip()
        sal_txt = self.entries["Salaire de base (DH)"].get().strip().replace(",", ".")
        try:
            salaire = float(sal_txt) if sal_txt else 0.0
        except ValueError:
            messagebox.showerror("Erreur", "Le salaire doit être un nombre.")
            return

        ms_txt = self.entries["Masse statutaire (h/semaine)"].get().strip().replace(",", ".")
        try:
            masse = float(ms_txt) if ms_txt else None
            if masse is not None and not 0 <= masse <= 80:
                raise ValueError
        except ValueError:
            messagebox.showerror("Erreur", "La masse statutaire doit être un nombre d'heures par semaine (ex. 26).")
            return

        if not nom or not prenom:
            messagebox.showerror("Erreur", "Le nom et le prénom sont obligatoires.")
            return

        with get_db_connection() as conn:
            cursor = conn.cursor()
            try:
                cursor.execute('''
                    INSERT INTO personnel (nom, prenom, cin, specialite, fonction, echelle, categorie, salaire, masse_statutaire)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                ''', (nom, prenom, cin, spec, fn, grd, lieu, salaire, masse))
                conn.commit()
                messagebox.showinfo("Succès", "Nouveau membre ajouté avec succès !")
                self.on_save_callback()
                self.destroy()
            except sqlite3.IntegrityError:
                messagebox.showerror("Erreur", "Le CIN/Matricule existe déjà pour un autre agent.")



# ------------------------------------------------------------------
# FENETRE BULLETIN DE PAIE (a partir d'un bulletin scanne)
# Saisie des lignes de paie -> enregistrement -> attestation de salaire.
# Le scan (image/PDF) est joint a la fiche ; un OCR (Tesseract, si
# installe) peut pre-remplir les montants automatiquement.
# ------------------------------------------------------------------
class BulletinPaieWindow(ctk.CTkToplevel):
    GAINS = [("Salaire de Base", "salaire_base"), ("Rappel Salaire", "rappel_salaire"),
             ("Heures Supplémentaires", "hrs_supp"),
             ("Prime de Résidence", "prime_residence"), ("Rappel P. Résidence", "rappel_p_residence"),
             ("13ème mois", "treizieme_mois"), ("Indemnité de Transport", "indemnite_transport"),
             ("Indemnité de qualification", "indemnite_qualification"), ("Indemnité de logement", "indemnite_logement"),
             ("Formation Alternée", "formation_alternee"), ("Indemnité spéciale", "indemnite_speciale"),
             ("Alloc. Familiales", "alloc_familiales")]
    # A.D.I. (tranche obligatoire) est imprimee dans la colonne GAINS mais elle vient en DEDUCTION des retenues :
    # TOTAL RETENUES = somme des retenues - A.D.I.  (verifie sur les bulletins : brut et net concordent au centime)
    RETENUES = [("Retraite RCAR", "rcar"), ("Mutuelle", "mutuelle"), ("I.R", "ir"),
                ("Prêt", "pret"), ("Assurance vie", "assurance_vie"), ("Retraite RECORE", "recore"),
                ("A.D.I. : tranche (déduction)", "adi")]

    def __init__(self, parent, personnel_data, on_save=None):
        super().__init__(parent)
        self.title(f"Bulletin de paie — {personnel_data[1]} {personnel_data[2]}")
        self.geometry("560x760")
        self.grab_set()
        self.p_id = personnel_data[0]
        self.on_save = on_save
        self.scan_path = ""

        ctk.CTkLabel(self, text=f"Bulletin de paie\n{personnel_data[1].upper()} {personnel_data[2]}",
                     font=ctk.CTkFont(size=16, weight="bold")).pack(pady=10)

        # scan
        fs = ctk.CTkFrame(self, fg_color="transparent")
        fs.pack(fill="x", padx=20)
        ctk.CTkLabel(fs, text="Bulletin scanné :", font=ctk.CTkFont(weight="bold"), width=110, anchor="w").pack(side="left")
        self.lbl_scan = ctk.CTkLabel(fs, text="(aucun fichier)", font=ctk.CTkFont(size=11), text_color="#6b7a89")
        self.lbl_scan.pack(side="left", padx=6)
        ctk.CTkButton(fs, text="Choisir…", width=90, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=self.choisir_scan).pack(side="left", padx=4)
        ctk.CTkButton(fs, text="🔍 Lire le bulletin", width=130, fg_color="#6a4fb3", hover_color="#4e3885",
                      command=self.extraire_auto).pack(side="left", padx=4)

        ctk.CTkLabel(self, text="Mois de paie (ex : avril 2026) :", font=ctk.CTkFont(weight="bold")
                     ).pack(anchor="w", padx=20, pady=(10, 2))
        self.ent_mois = ctk.CTkEntry(self, placeholder_text="avril 2026")
        self.ent_mois.pack(fill="x", padx=20)

        scroll = ctk.CTkScrollableFrame(self)
        scroll.pack(fill="both", expand=True, padx=15, pady=8)
        self.ent = {}

        def section(titre):
            ctk.CTkLabel(scroll, text=titre, font=ctk.CTkFont(size=14, weight="bold"),
                         text_color=MAIN_COLOR).pack(anchor="w", pady=(8, 4))
        def ligne(parent, label, key):
            fr = ctk.CTkFrame(parent, fg_color="transparent")
            fr.pack(fill="x", pady=2)
            ctk.CTkLabel(fr, text=label + " :", width=200, anchor="w").pack(side="left")
            e = ctk.CTkEntry(fr, placeholder_text="0.00")
            e.pack(side="right", fill="x", expand=True)
            self.ent[key] = e

        section("GAINS")
        for label, key in self.GAINS:
            ligne(scroll, label, key)
        section("RETENUES")
        for label, key in self.RETENUES:
            ligne(scroll, label, key)

        self.lbl_tot = ctk.CTkLabel(self, text="", font=ctk.CTkFont(size=12, weight="bold"),
                                    text_color="#0e7c66")
        self.lbl_tot.pack(pady=(4, 0))
        for e in self.ent.values():
            e.bind("<KeyRelease>", lambda _e: self.calculer())

        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.pack(pady=10)
        ctk.CTkButton(btns, text="💾  Enregistrer le bulletin", width=240, fg_color="#1b8a5a",
                      hover_color="#0f5c3a", command=self.save).pack(side="left", padx=6)
        ctk.CTkButton(btns, text="Annuler", width=100, fg_color="#6c757d", hover_color="#495057",
                      command=self.destroy).pack(side="left", padx=6)

        self.charger()

    # ---------- donnees ----------
    @staticmethod
    def _f(v):
        return parse_money(v)

    def _totaux(self):
        """(TOTAL GAINS, TOTAL RETENUES, NET A PAYER) calcules comme sur le bulletin officiel."""
        g = lambda k: self._f(self.ent[k].get())
        tg = sum(g(k) for _l, k in self.GAINS)
        tr = sum(g(k) for _l, k in self.RETENUES if k != "adi") - g("adi")
        return round(tg, 2), round(tr, 2), round(tg - tr, 2)

    def calculer(self):
        tg, tr, net = self._totaux()
        self.lbl_tot.configure(text=f"Salaire brut (TOTAL GAINS) : {tg:,.2f} DHS   ·   "
                                    f"TOTAL RETENUES : {tr:,.2f} DHS   ·   "
                                    f"NET A PAYER : {net:,.2f} DHS".replace(",", " "))
        return tg, tr

    def choisir_scan(self):
        p = filedialog.askopenfilename(title="Bulletin de paie scanné",
                                       filetypes=[("Images / PDF", "*.png *.jpg *.jpeg *.pdf *.bmp *.tif *.tiff"),
                                                  ("Tous", "*.*")])
        if not p:
            return
        try:
            dest_dir = os.path.join(APP_DATA_DIR, "bulletins_scans")
            os.makedirs(dest_dir, exist_ok=True)
            ext = os.path.splitext(p)[1]
            dest = os.path.join(dest_dir, f"bulletin_{self.p_id}{ext}")
            shutil.copy(p, dest)
            self.scan_path = dest
            self.lbl_scan.configure(text=os.path.basename(p), text_color="#0e7c66")
            # extraction automatique des montants depuis le bulletin (PDF ou OCR)
            self._override_totals = None
            self.after(300, self.extraire_auto)
        except Exception as e:
            messagebox.showerror("Erreur", f"Impossible de copier le scan :\n{e}")

    # ---------- lecture automatique du bulletin de l'etablissement ----------
    @staticmethod
    def _lire_texte_pdf(path):
        """Extrait le texte d'un PDF (pypdf / PyPDF2 / fitz / pdfminer).
        Retourne None si aucun lecteur n'est installe."""
        for modname in ("pypdf", "PyPDF2"):
            try:
                mod = __import__(modname, fromlist=["PdfReader"])
                txt = "\n".join(pg.extract_text() or "" for pg in mod.PdfReader(path).pages)
                if txt.strip():
                    return txt
            except ImportError:
                continue
            except Exception:
                return None
        try:
            import fitz
            def _gt(pg):
                try: return pg.get_text("text", sort=True)      # ordre de lecture ligne par ligne
                except TypeError: return pg.get_text()
            txt = "\n".join(_gt(pg) for pg in fitz.open(path))
            if txt.strip():
                return txt
        except ImportError:
            pass
        except Exception:
            return None
        try:
            from pdfminer.high_level import extract_text
            from pdfminer.layout import LAParams
            txt = extract_text(path, laparams=LAParams(boxes_flow=None, line_margin=0.1, char_margin=60, word_margin=0.15))
            if txt and txt.strip():
                return txt
        except ImportError:
            pass
        except Exception:
            return None
        return None

    def extraire_auto(self):
        """Lit le bulletin joint : PDF -> extraction directe du texte ;
        image -> OCR (Tesseract). Remplit automatiquement les montants."""
        if not self.scan_path:
            messagebox.showinfo("Bulletin", "Choisissez d'abord le bulletin scanné.")
            return
        txt = None
        if self.scan_path.lower().endswith(".pdf"):
            try:
                txt = self._lire_texte_pdf(self.scan_path)
            except Exception:
                txt = None
            if not txt:
                messagebox.showwarning(
                    "Lecteur PDF manquant",
                    "Impossible de lire le texte du PDF.\n\n"
                    "Installez une bibliothèque de lecture PDF (une seule fois) :\n"
                    "    pip install pypdf\n\n"
                    "Puis réessayez « 🔍 Lire le bulletin ».")
                return
        if txt and txt.strip():
            self._remplir_depuis_texte(txt)
        else:
            # image scannée (pas de couche texte) -> OCR
            self.ocr_scan()

    @staticmethod
    def _to_float(s):
        return float(str(s).replace("\xa0", "").replace(" ", "").replace(",", "."))

    @staticmethod
    def _parse_totaux(txt):
        """Totaux officiels imprimes en bas du bulletin (floats) : TOTAL GAINS, TOTAL RETENUES, NET A PAYER.
        Independant de la facon dont le lecteur PDF decoupe les lignes (texte aplati)."""
        flat = " ".join(txt.replace("\xa0", " ").split())
        mt = r"\d{1,3}(?: \d{3})*,\d{2}"
        tot = {}
        m = re.search(r"BASE\s*RETRAITE(.*?)(?:SOLDE\s*CONG|NET\s*A\s*PAYER|$)", flat, re.I)
        if m:
            nums = re.findall(mt, m.group(1))
            if len(nums) == 5:   # base retraite, salaire brut, sal. imposable, total gains, total retenues
                (tot["base_retraite"], tot["brut"], tot["imposable"],
                 tot["gains"], tot["retenues"]) = (BulletinPaieWindow._to_float(x) for x in nums)
        m = re.search(r"NET\s*A\s*PAYER\s*(" + mt + ")", flat, re.I)
        if m:
            tot["net"] = BulletinPaieWindow._to_float(m.group(1))
        return tot

    @staticmethod
    def _options_montant(ln):
        """Dernier montant d'une ligne de rubrique. Retourne [valeur_milliers_fusionnee, valeur_seule] quand
        c'est ambigu (« ElAdha 26 100,00 » peut etre 26 100,00 ou 100,00), sinon [valeur]. Les taux (6,000) sont ignores."""
        clean = re.sub(r"\d+,\d{3}(?!\d)", " ", ln.replace("\xa0", " "))
        toks = clean.split()
        res = []
        for i, t in enumerate(toks):
            if re.fullmatch(r"\d+,\d{2}", t):
                v = float(t.replace(",", "."))
                if i and re.fullmatch(r"\d{1,3}", toks[i - 1]) and re.fullmatch(r"\d{3},\d{2}", t):
                    res = [float(toks[i - 1] + t.replace(",", ".")), v]
                else:
                    res = [v]
        return res

    def _remplir_depuis_texte(self, txt):
        """Parse le bulletin de l'etablissement puis CONTROLE le resultat avec les totaux imprimes
        (TOTAL GAINS / TOTAL RETENUES / NET A PAYER). Les cas ambigus sont resolus grace a ces totaux."""
        import itertools, unicodedata
        def norm(s):
            return unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode().casefold()
        noms_mois = ["janvier", "février", "mars", "avril", "mai", "juin", "juillet",
                     "août", "septembre", "octobre", "novembre", "décembre"]
        RULES = [
            (("salairedebase",), "salaire_base"),
            (("rappelsalaire",), "rappel_salaire"),
            (("rappelpresidence", "rappelderesidence"), "rappel_p_residence"),
            (("primeresidence",), "prime_residence"),
            (("13eme", "13ememois", "treiziememois"), "treizieme_mois"),
            (("hrssupp", "hrssupplementaire", "hssupp"), "hrs_supp"),
            (("indlogement",), "indemnite_logement"),
            (("indemnitequalif",), "indemnite_qualification"),
            (("indemnitespeciale",), "indemnite_speciale"),
            (("allocfamiliales", "allocfamil"), "alloc_familiales"),
            (("indtransport",), "indemnite_transport"),
            (("rcar",), "rcar"),
            (("mutuelle",), "mutuelle"),
            (("assurancevie",), "assurance_vie"),
            (("pret",), "pret"),
            (("recore",), "recore"),
            (("impot",), "ir"),
            (("tranche",), "adi"),            # « A.D.I. : tranche obl » (et non « adi », present dans AGADIR...)
        ]
        lines = [l.strip() for l in txt.splitlines() if l.strip()]
        totals = self._parse_totaux(txt)

        # --- periode de paie (MM/AA, MM <= 12) ---
        mois = None
        for ln in lines:
            for m in re.finditer(r"(\d{2})/(\d{2})(?!\d)", ln):
                mm, yy = int(m.group(1)), int(m.group(2))
                if 1 <= mm <= 12 and yy <= 30:
                    mois = f"{noms_mois[mm - 1]} 20{yy:02d}"

        # --- rubriques : on ne lit que les lignes qui commencent par un code rubrique (3 chiffres) ---
        has_codes = sum(1 for l in lines if re.match(r"\d{3}\s+\S", l)) >= 5
        entries = []                                   # (champ, options, choix_par_defaut)
        for idx, ln in enumerate(lines):
            if has_codes and not re.match(r"\d{3}\s+\S", ln):
                continue
            nln = norm(ln).replace(" ", "").replace(".", "")
            for keys, champ in RULES:
                if any(kk in nln for kk in keys):
                    opts = self._options_montant(ln.replace("|", " "))
                    if not opts:                                   # valeur sur la ligne suivante (autre mise en page)
                        for off in (1, 2):
                            if idx + off < len(lines):
                                cand = lines[idx + off].replace("|", " ").strip()
                                a2 = self._options_montant(cand)
                                if a2 and re.fullmatch(r"[\d\s.,]+", cand):
                                    opts = a2
                    if opts:
                        # « Pret Aid ElAdha 26 100,00 » : le 26 fait partie du libelle -> 100,00
                        entries.append((champ, opts, 1 if (len(opts) > 1 and champ == "pret") else 0))
                    break

        gkeys = {k for _l, k in self.GAINS}
        rkeys = {k for _l, k in self.RETENUES}

        def valeurs(choix):
            v = {}
            for (champ, opts, _d), c in zip(entries, choix):
                v[champ] = v.get(champ, 0.0) + opts[c]
            return v

        def totaux_de(v):
            tg = sum(v.get(k, 0.0) for k in gkeys)
            tr = sum(v.get(k, 0.0) for k in rkeys if k != "adi") - v.get("adi", 0.0)
            return tg, tr

        choix = [d for _c, _o, d in entries]
        corrige = False
        if "gains" in totals and "retenues" in totals:
            def ok(ch):
                tg, tr = totaux_de(valeurs(ch))
                return abs(tg - totals["gains"]) < 0.02 and abs(tr - totals["retenues"]) < 0.02
            if not ok(choix):                              # resolution des ambiguites grace aux totaux du bulletin
                amb = [i for i, e in enumerate(entries) if len(e[1]) > 1][:12]
                trouve = None
                for r in range(1, min(4, len(amb)) + 1):
                    for combo in itertools.combinations(amb, r):
                        ch = list(choix)
                        for i in combo:
                            ch[i] = 1 - ch[i]
                        if ok(ch):
                            trouve = ch
                            break
                    if trouve:
                        break
                if trouve:
                    choix, corrige = trouve, True

        found = valeurs(choix)
        # on repart de zero : sinon les montants d'un ancien bulletin (rappels, 13e mois...) restent dans le formulaire
        for e in self.ent.values():
            e.delete(0, "end")
        n = 0
        for key, val in found.items():
            if key in self.ent and abs(val) > 0.0001:
                self.ent[key].insert(0, "%.2f" % val)
                n += 1
        if mois:
            self.ent_mois.delete(0, "end"); self.ent_mois.insert(0, mois)
        self._override_totals = totals or None
        self.calculer()

        # --- controle final avec les totaux imprimes sur le bulletin ---
        tg, tr, net = self._totaux()
        fm = lambda x: f"{x:,.2f}".replace(",", " ")
        msg = f"{n} rubrique(s) extraite(s) automatiquement."
        if mois:
            msg += f"\nPériode : {mois}"
        titre, fct = "Bulletin lu", messagebox.showinfo
        if "gains" in totals and "retenues" in totals:
            ecarts = []
            if abs(tg - totals["gains"]) > 0.02:
                ecarts.append(f"TOTAL GAINS : lu {fm(tg)}  ≠  bulletin {fm(totals['gains'])}")
            if abs(tr - totals["retenues"]) > 0.02:
                ecarts.append(f"TOTAL RETENUES : lu {fm(tr)}  ≠  bulletin {fm(totals['retenues'])}")
            if "net" in totals and abs(net - totals["net"]) > 0.02:
                ecarts.append(f"NET A PAYER : lu {fm(net)}  ≠  bulletin {fm(totals['net'])}")
            if ecarts:
                titre, fct = "Bulletin lu : ÉCART DÉTECTÉ", messagebox.showwarning
                msg += "\n\n⚠ Les montants lus ne correspondent pas aux totaux du bulletin :\n  - " + "\n  - ".join(ecarts)
                msg += "\n\nCorrigez les lignes concernées avant d'enregistrer."
            else:
                msg += (f"\n\n✅ Contrôle réussi : les montants correspondent au bulletin.\n"
                        f"Salaire brut : {fm(totals['gains'])} DHS\nTOTAL RETENUES : {fm(totals['retenues'])} DHS")
                if "net" in totals:
                    msg += f"\nNET A PAYER : {fm(totals['net'])} DHS"
                if corrige:
                    msg += "\n(un montant ambigu a été corrigé automatiquement grâce aux totaux)"
        else:
            msg += "\n\nTotaux du bulletin introuvables : impossible de contrôler automatiquement."
            msg += "\nVérifiez chaque valeur avant d'enregistrer."
        fct(titre, msg)

    def ocr_scan(self):
        """Pre-remplit les montants depuis le scan (Tesseract requis)."""
        if not self.scan_path:
            messagebox.showinfo("OCR", "Choisissez d'abord le bulletin scanné.")
            return
        try:
            import pytesseract
            from PIL import Image
        except ImportError:
            messagebox.showerror("OCR indisponible",
                                 "Le module 'pytesseract' (et Tesseract OCR) n'est pas installé.\n"
                                 "Installez :  pip install pytesseract pillow\n"
                                 "puis Tesseract : https://github.com/UB-Mannheim/tesseract/wiki")
            return
        try:
            txt = pytesseract.image_to_string(Image.open(self.scan_path), lang="fra")
        except Exception as e:
            messagebox.showerror("OCR", f"Lecture impossible :\n{e}")
            return
        import re, unicodedata
        def norm(s):
            return " ".join(unicodedata.normalize("NFKD", s).encode("ascii", "ignore")
                            .decode().casefold().split())
        mapping = {"salaire de base": "salaire_base", "rappel salaire": "rappel_salaire",
                   "prime de residence": "prime_residence", "residence": "prime_residence",
                   "13 eme": "treizieme_mois", "13eme": "treizieme_mois", "transport": "indemnite_transport",
                   "qualification": "indemnite_qualification", "logement": "indemnite_logement",
                   "alternee": "formation_alternee", "speciale": "indemnite_speciale",
                   "rcar": "rcar", "mutuelle": "mutuelle", " assurance vie": "assurance_vie",
                   "recore": "recore", "adi": "adi"}
        trouves = 0
        for ln in txt.splitlines():
            nln = norm(ln)
            nums = re.findall(r"\d{1,3}(?:[ .]\d{3})*(?:[,.]\d{1,2})?", ln)
            if not nums:
                continue
            val = nums[-1].replace(" ", "").replace(",", ".")
            for kw, key in mapping.items():
                if kw in nln and key in self.ent:
                    self.ent[key].delete(0, "end"); self.ent[key].insert(0, val)
                    trouves += 1
                    break
        self.calculer()
        messagebox.showinfo("OCR terminé", f"{trouves} montant(s) détecté(s).\nVérifiez chaque valeur avant d'enregistrer.")

    def charger(self):
        with get_db_connection() as conn:
            d = fetch_bulletin(conn, self.p_id)
        if not d:
            return
        if d.get("mois"):
            self.ent_mois.insert(0, d["mois"])
        if d.get("scan_path") and os.path.exists(d["scan_path"]):
            self.scan_path = d["scan_path"]
            self.lbl_scan.configure(text=os.path.basename(d["scan_path"]), text_color="#0e7c66")
        for _l, key in self.GAINS + self.RETENUES:
            if parse_money(d.get(key)):
                self.ent[key].insert(0, format_money(d[key]))
        self.calculer()

    def save(self):
        mois = self.ent_mois.get().strip() or mois_fr()
        tg, tr, net_val = self._totaux()
        ov = getattr(self, "_override_totals", None) or {}
        if "gains" in ov and "retenues" in ov and (abs(tg - ov["gains"]) > 0.02 or abs(tr - ov["retenues"]) > 0.02):
            fm = lambda x: f"{x:,.2f}".replace(",", " ")
            if not messagebox.askyesno(
                    "Écart avec le bulletin",
                    "Les montants saisis ne correspondent pas aux totaux du bulletin joint :\n\n"
                    f"TOTAL GAINS : {fm(tg)}  (bulletin : {fm(ov['gains'])})\n"
                    f"TOTAL RETENUES : {fm(tr)}  (bulletin : {fm(ov['retenues'])})\n\n"
                    "L'attestation de salaire sera fausse.\nEnregistrer quand même ?", parent=self):
                return
        cols = [k for _l, k in self.GAINS + self.RETENUES]
        vals = {}
        for _l, k in self.GAINS + self.RETENUES:
            try:
                vals[k] = parse_money(self.ent[k].get(), strict=True)
            except ValueError:
                messagebox.showerror("Montant invalide", f"« {_l} » : « {self.ent[k].get()} » n'est pas un montant valide.", parent=self)
                return
        with get_db_connection() as conn:
            conn.execute("DELETE FROM bulletin_paie WHERE personnel_id=?", (self.p_id,))
            conn.execute("INSERT INTO bulletin_paie (personnel_id, mois, scan_path, " +
                         ", ".join(cols) + ", total_gains, total_retenues, net_a_payer) VALUES (?,?,?," +
                         ",".join("?" * (len(cols) + 3)) + ")",
                         (self.p_id, mois, self.scan_path,
                          *[vals[k] for k in cols], round(tg, 2), round(tr, 2), round(net_val, 2)))
            conn.commit()
        messagebox.showinfo("Succès", "Bulletin de paie enregistré !\n\nVous pouvez maintenant générer l'attestation de salaire.")
        if self.on_save:
            self.on_save()
        self.destroy()


# ------------------------------------------------------------------
# APPLICATION PRINCIPALE
# ------------------------------------------------------------------
class TimeTableFrame(tk.Frame):
    """Module Emploi du temps (Time Table) integre au logiciel : menus, tableau de bord,
    filieres, groupes, formateurs, espaces et grilles d'emploi du temps."""
    AUTO = EMPLOI_FILE      # sauvegarde automatique (dossier AppData, avec copies de securite)

    def __init__(self, master, on_quit=None, mode="directeur", on_switch=None):
        super().__init__(master)
        self.on_quit = on_quit
        self.mode, self.on_switch = mode, on_switch            # "directeur" ou "enote"
        self.sel_e = None                                      # espace (salle/atelier) selectionne dans les panneaux de droite
        self.sel_g = None                                      # groupe selectionne dans les panneaux de droite
        self.AUTO = EMPLOI_FILE if mode == "directeur" else ENOTE_EMPLOI_FILE
        self.D, self.path, self.tabs, self.canv, self.sel_f, self.drag = tt_blank(), None, {}, {}, None, None
        self.psel, self.sel_state, self._pw_cvs = {}, {"kind": "frm", "id": None}, []   # espace d'impression / onglet Emploi
        try:
            with open(self.AUTO, encoding="utf-8") as fh:
                x = json.load(fh)
            d = {**tt_blank(), **x}
            d["v"] = x.get("v")
            self.D = tt_migrate(d)
        except FileNotFoundError:
            if self.mode == "enote":
                self._seed_enote()                  # 1re ouverture de l'emploi eNote : on reprend groupes/espaces/formateurs
            # emploi du directeur : premiere ouverture = emploi du temps vide
        except Exception:
            logger.exception("Lecture de %s impossible", self.AUTO)
            try:
                shutil.copy2(self.AUTO, f"{self.AUTO}.corrompu-{datetime.now():%Y%m%d-%H%M%S}")   # on garde le fichier fautif
            except OSError:
                pass
            bk = latest_backup("emploi_data", ".json") if self.mode == "directeur" else None
            if bk:
                try:
                    with open(bk, encoding="utf-8") as fh:
                        x = json.load(fh)
                    d = {**tt_blank(), **x}; d["v"] = x.get("v"); self.D = tt_migrate(d)
                    messagebox.showinfo("Emploi du temps", "Le fichier de l'emploi du temps était illisible.\n"
                                        f"La dernière sauvegarde a été restaurée ({os.path.basename(bk)}).")
                except Exception:
                    logger.exception("Restauration depuis %s impossible", bk)
        self.sync_formateurs()
        self.build_menus()
        self.nb = ttk.Notebook(self); self.nb.pack(fill="both", expand=True)
        self.nb.bind("<Double-Button-1>", self.close_tab); self.nb.bind("<Button-2>", self.close_tab)
        top = self.winfo_toplevel()
        for seq, fn in [("n", self.new), ("o", self.open_file), ("s", self.save), ("S", self.save_as), ("p", self.print_),
                        ("P", lambda: self.open("print")), ("q", self.quitter), ("g", lambda: self.open("groupes")),
                        ("f", lambda: self.open("formateurs")), ("e", lambda: self.open("espaces"))]:
            top.bind(f"<Control-{seq}>", lambda ev, fn=fn: fn() if self.winfo_exists() else None, add="+")
        self.open("home"); self.set_title()
        if self.mode == "enote" and not os.path.exists(self.AUTO):
            self.autosave()                         # cree le fichier de l'emploi eNote des la 1re ouverture

    def _seed_enote(self):
        """Emploi eNote vide : reprend filieres, groupes, formateurs et espaces de l'emploi du directeur (sans les seances)."""
        try:
            with open(EMPLOI_FILE, encoding="utf-8") as fh:
                x = json.load(fh)
            x["seances"] = []
            d = {**tt_blank(), **x}; d["v"] = x.get("v")
            self.D = tt_migrate(d)
        except Exception:
            self.D = tt_blank()
        self.D["seances"] = []
        self.D["file"] = "emploi_enote"

    # ---------- absences des formateurs (jours grises dans la grille) ----------
    def sem_lundi(self):
        d = getattr(self, "sem_abs", None) or datetime.now().date()
        return d - timedelta(days=d.weekday())

    def abs_list(self, fid):
        """[(date_debut, date_fin, motif)] des absences enregistrees pour ce formateur (comparaison des noms sans accents ni ordre)."""
        o = tt_get(self.D, "formateurs", fid) if fid is not None else None
        if not o:
            return []
        pre = o.get("prenom", "") or ""
        key = lambda t: frozenset(tt_norm(t).split())
        names = {key(tt_fname(o)), key(f"{pre} {o['nom']}"), key(f"{o['nom']} {pre}")}
        mine = []
        try:
            with get_db_connection() as conn:
                cur = conn.cursor()
                cur.execute("SELECT p.nom, p.prenom, a.motif, a.date_debut, a.date_fin FROM absences a JOIN personnel p ON a.personnel_id = p.id")
                rows = cur.fetchall()
            for nom, prenom, motif, d1, d2 in rows:
                if key(f"{prenom or ''} {nom}") in names:
                    try:
                        mine.append((datetime.strptime(d1, "%d/%m/%Y").date(), datetime.strptime(d2, "%d/%m/%Y").date(), motif))
                    except (ValueError, TypeError):
                        pass
        except Exception:
            logger.exception("Lecture des absences impossible")
        return mine

    def abs_days(self, fid):
        """{jour 0-5 : motif} pour les jours de la semaine choisie ou le formateur est absent (table des absences + formations)."""
        o = tt_get(self.D, "formateurs", fid) if fid is not None else None
        if not o:
            return {}
        pre = o.get("prenom", "") or ""
        names = {tt_norm(tt_fname(o)), tt_norm(f"{pre} {o['nom']}"), tt_norm(f"{o['nom']} {pre}")}
        mine, lundi, res = self.abs_list(fid), self.sem_lundi(), {}
        for d in range(6):
            j = lundi + timedelta(days=d)
            hit = next((m for a, b, m in mine if a <= j <= b), None)
            if hit is None:
                try:
                    if names & tt_absents(j): hit = "Absent"          # autres sources (formations enregistrees...)
                except Exception:
                    pass
            if hit: res[d] = hit
        return res

    def abs_first_week(self, fid):
        """Lundi de la semaine en cours si le formateur y est absent, sinon de sa prochaine absence ; sinon la semaine en cours."""
        today = datetime.now().date(); lundi = today - timedelta(days=today.weekday())
        fin_sem = lundi + timedelta(days=5)
        mine = self.abs_list(fid)
        if any(a <= fin_sem and b >= lundi for a, b, m in mine):
            return lundi
        fut = sorted(a for a, b, m in mine if a > fin_sem)
        return (fut[0] - timedelta(days=fut[0].weekday())) if fut else lundi

    def abs_ok(self, fid, day):
        """Refuse de placer une seance un jour ou le formateur est absent (semaine choisie). Renvoie True si le placement est permis."""
        m = self.abs_days(fid).get(day) if fid is not None else None
        if not m:
            return True
        o = tt_get(self.D, "formateurs", fid)
        j = self.sem_lundi() + timedelta(days=day)
        messagebox.showwarning("Formateur absent",
                               f"{tt_fname(o)} est absent(e) le {TT_DAYS[day]} {j:%d/%m/%Y} : {m}.\n\n"
                               "Impossible de placer une séance ce jour-là.")
        return False

    def switch_mode(self, m):
        """Bascule entre l'emploi du directeur et l'emploi eNote (chacun a son propre fichier)."""
        if m == self.mode or not self.on_switch:
            return
        self.autosave()
        self.on_switch(m)

    def quitter(self):
        backup_data()
        if self.on_quit: self.on_quit()

    # ---------- menus ----------
    def build_menus(self):
        bar = tk.Frame(self, bg="#ffffff"); bar.pack(fill="x")
        tk.Frame(self, height=1, bg="#d5dce5").pack(fill="x")          # filet sous la barre
        def mb(label, **kw):
            b = tk.Menubutton(bar, text=label, bg="#ffffff", fg="#33475b",
                              activebackground="#e8eef5", activeforeground="#0056b3",
                              relief="flat", padx=16, pady=9,
                              font=("Segoe UI", 10), cursor="hand2")
            b.pack(side="left"); m = tk.Menu(b, tearoff=0, activebackground="#0056b3",
                                             activeforeground="white", **kw); b["menu"] = m
            return m
        fm = mb("Fichier")
        for it in [("Nouveau", "Ctrl+N", self.new), ("Ouvrir", "Ctrl+O", self.open_file), ("Enregistrer", "Ctrl+S", self.save),
                   ("Enregistrer sous ...", "Ctrl+Maj+S", self.save_as), *([("Importer séances eNote (Excel)...", "", self.import_enote)] if self.mode == "enote" else []), None, ("Imprimer", "Ctrl+P", self.print_),
                   ("Espace d'impression", "Ctrl+Maj+P", lambda: self.open("print")), None, ("Quitter", "Ctrl+Q", self.quitter)]:
            if it is None: fm.add_separator()
            else: fm.add_command(label=it[0], accelerator=it[1], command=it[2])
        for lab, k in [("Groupes", "groupes"), ("Formateurs", "formateurs")]:
            setattr(self, "m_" + k, mb(lab, postcommand=lambda k=k: self.fill_menu(k)))
        self.m_esp = mb("Espaces", postcommand=self.fill_esp)
        pm = mb("Paramètres")
        for lab, key, acc in [("Etablissement", "etab", ""), ("Filières", "filieres", ""), ("Groupes", "groupes", "Ctrl+G"),
                              ("Formateurs", "formateurs", "Ctrl+F"), ("Espace", "espaces", "Ctrl+E"), ("Matrice", "matrice", "")]:
            pm.add_command(label=lab, accelerator=acc, command=lambda key=key: self.open(key))
        pm.add_command(label="Couleurs des salles / ateliers", command=self.couleurs_dialog)

        # Actions = exactement le meme style d'ecriture que les menus
        def act(label, cmd):
            tk.Button(bar, text=label, bg="#ffffff", fg="#33475b",
                      activebackground="#e8eef5", activeforeground="#0056b3",
                      relief="flat", bd=0, font=("Segoe UI", 10),
                      padx=16, pady=9, cursor="hand2", command=cmd).pack(side="left", padx=(8, 0))
        act("Emploi", lambda: self.open("sel"))
        if self.mode == "enote":                                                  # seul bouton propre a l'emploi eNote
            act("Importer séances eNote", self.import_enote)
        act("Espace d'impression", lambda: self.open("print"))
        self.lbl_file = tk.Label(bar, bg="#ffffff", fg="#6b7a89", font=("Segoe UI", 9, "italic"))
        self.lbl_file.pack(side="right", padx=12)

    def fill_menu(self, k):
        m = getattr(self, "m_" + k); m.delete(0, "end")
        pre = "grp" if k == "groupes" else "frm"
        for x in self.D[k]:
            m.add_command(label=tt_fname(x) if k == "formateurs" else x["nom"], command=lambda i=x["id"]: self.open(f"{pre}:{i}"))
        if not self.D[k]: m.add_command(label="(aucun élément)", state="disabled")

    def fill_esp(self):
        self.m_esp.delete(0, "end")
        for t in ("Salle", "Atelier"):
            sub = tk.Menu(self.m_esp, tearoff=0)
            for e in [e for e in self.D["espaces"] if e["type"] == t]:
                sub.add_command(label=e["nom"], command=lambda i=e["id"]: self.open(f"esp:{i}"))
            self.m_esp.add_cascade(label=t, menu=sub)

    # ---------- onglets ----------
    def ttitle(self, key):
        if ":" not in key:
            return {"home": "Accueil", "etab": "Etablissement", "filieres": "Filières", "groupes": "Groupes",
                    "formateurs": "Formateurs", "espaces": "Espaces",
                    "sel": "Emploi", "print": "Espace d'impression"}[key]
        k, i = key.split(":"); coll = TT_KIND[k][0]; o = tt_get(self.D, coll, int(i))
        return tt_fname(o) if k == "frm" else o["nom"]

    def valid(self, key):
        return ":" not in key or tt_get(self.D, TT_KIND[key.split(":")[0]][0], int(key.split(":")[1])) is not None

    def open(self, key):
        if key == "matrice":
            if not self.D["espaces"]: return messagebox.showinfo("Time Table", "Ajoute d'abord un espace.")
            key = f"esp:{self.D['espaces'][0]['id']}"
        if key not in self.tabs:
            if key.startswith("frm:"): self.sem_abs = None      # nouvel onglet formateur : ouvrir sur la semaine de son absence
            f = ttk.Frame(self.nb); self.tabs[key] = f; self.nb.add(f, text=self.ttitle(key)); self.build(key, f)
        self.nb.select(self.tabs[key])

    def build(self, key, f):
        self.canv.pop(key, None)
        if key == "home": self.build_home(f)
        elif key == "etab": self.build_etab(f)
        elif key == "sel": self.build_sel(f)
        elif key == "print": self.build_print(f)
        elif ":" in key: self.build_tt(f, key)
        else: self.build_crud(f, key)

    def refresh(self):
        for key in list(self.tabs):
            f = self.tabs[key]
            if not self.valid(key):
                self.nb.forget(f); f.destroy(); del self.tabs[key]; continue
            for w in f.winfo_children(): w.destroy()
            self.build(key, f); self.nb.tab(f, text=self.ttitle(key))
        self.set_title()
        self.autosave()

    def autosave(self):
        try:
            atomic_write_json(self.AUTO, self.D)
        except Exception:
            logger.exception("Sauvegarde automatique de l'emploi du temps impossible (%s)", self.AUTO)
            if not getattr(self, "_autosave_warned", False):      # un seul avertissement par session
                self._autosave_warned = True
                messagebox.showwarning("Sauvegarde automatique",
                                       f"L'emploi du temps n'a pas pu être enregistré automatiquement.\n\nFichier : {self.AUTO}\n\n"
                                       "Utilisez Fichier > Enregistrer sous pour ne pas perdre votre travail.")

    def cur(self):
        w = self.nb.nametowidget(self.nb.select())
        return next((k for k, f in self.tabs.items() if f is w), None)

    def close_tab(self, e):
        try: w = self.nb.nametowidget(self.nb.tabs()[self.nb.index(f"@{e.x},{e.y}")])
        except tk.TclError: return
        key = next((k for k, f in self.tabs.items() if f is w), None)
        if key and key != "home": self.nb.forget(w); w.destroy(); del self.tabs[key]

    def set_title(self): self.lbl_file.config(text=f"Fichier : {self.D['file']}")
    def mode_label(self): return "Emploi établi par le directeur" if self.mode == "directeur" else "Emploi établi d'après eNote"
    def uid(self): self.D["n"] += 1; return self.D["n"]

    # ---------- fichier ----------
    def new(self):
        if messagebox.askyesno("Nouveau", "Créer un nouveau fichier ? Les données non enregistrées seront perdues."):
            self.D, self.path, self.sel_f = tt_blank(), None, None
            self.sync_formateurs()
            for k in [k for k in self.tabs if k != "home"]:
                self.nb.forget(self.tabs[k]); self.tabs.pop(k).destroy()
            self.refresh()

    def open_file(self):
        p = filedialog.askopenfilename(filetypes=[("Fichiers Time Table (*.tk, *.json)", "*.tk *.json"),
                                                   ("Fichier TK", "*.tk"), ("JSON", "*.json"), ("Tous", "*.*")])
        if not p: return
        try:
            x = tt_read_file(p)
            d = {**tt_blank(), **x}; d["v"] = x.get("v"); self.D = tt_migrate(d)
        except Exception:
            return messagebox.showerror("Ouvrir", "Fichier non valide.")
        self.path = p; self.D["file"] = os.path.splitext(os.path.basename(p))[0]; self.refresh()

    def save(self):
        if not self.path: return self.save_as()
        try:
            atomic_write_json(self.path, self.D, indent=1)
        except OSError as ex:
            logger.exception("Enregistrement impossible : %s", self.path)
            messagebox.showerror("Enregistrer", f"Impossible d'enregistrer le fichier :\n{ex}")

    def save_as(self):
        p = filedialog.asksaveasfilename(defaultextension=".tk", initialfile=self.D["file"],
                                       filetypes=[("Fichier TK", "*.tk"), ("Time Table JSON", "*.json")])
        if p:
            self.path = p; self.D["file"] = os.path.splitext(os.path.basename(p))[0]; self.save(); self.refresh()

    def print_(self):
        cv = self.canv.get(self.cur())
        if not cv: return messagebox.showinfo("Imprimer", "Ouvre l'emploi du temps d'un espace, d'un groupe ou d'un formateur.")
        p = filedialog.asksaveasfilename(defaultextension=".ps", filetypes=[("PostScript (imprimable)", "*.ps")])
        if p: cv.postscript(file=p, colormode="color", width=TT_LW + TT_Q * TT_QW + 4, height=TT_HH + 6 * TT_RH + 4)

    # ---------- onglet "Emploi" : choisir un formateur / groupe / espace et afficher son emploi ----------
    def list_items(self, kind):
        """[(id, libelle)] tries par libelle, pour 'frm' (formateurs), 'grp' (groupes) ou 'esp' (espaces)."""
        coll = TT_KIND[kind][0]
        lst = [(x["id"], tt_fname(x) if kind == "frm" else x["nom"]) for x in self.D[coll]]
        return sorted(lst, key=lambda t: tt_norm(t[1]))

    def build_sel(self, f):
        st = self.sel_state; ids = []
        bar = tk.Frame(f, bg=TT_BLUE); bar.pack(fill="x", padx=6, pady=(6, 0))
        tk.Label(bar, text="Emploi du temps", bg=TT_BLUE, fg="white", font=("Segoe UI", 15, "bold"), padx=10, pady=6).pack(side="left")
        pick = ttk.Frame(f); pick.pack(fill="x", padx=6, pady=8)
        kv = tk.StringVar(value=st["kind"])
        ttk.Label(pick, text="Afficher l'emploi du :").pack(side="left")
        cb = ttk.Combobox(pick, state="readonly", width=42)
        holder = ttk.Frame(f); holder.pack(fill="both", expand=True)

        def clear():
            for w in holder.winfo_children(): w.destroy()
            self.canv.pop("sel", None)

        def fill():
            lst = self.list_items(kv.get()); ids[:] = [i for i, _ in lst]
            cb["values"] = [l for _, l in lst]; cb.set("")

        def show(*_):
            clear()
            n = cb.current()
            if n < 0: return
            st["kind"], st["id"] = kv.get(), ids[n]
            self.build_tt(holder, f"{kv.get()}:{ids[n]}", "sel")

        def on_kind():
            st["id"] = None; fill(); clear()

        for lab, k in (("Formateur", "frm"), ("Groupe", "grp"), ("Espace / Salle", "esp")):
            ttk.Radiobutton(pick, text=lab, value=k, variable=kv, command=on_kind).pack(side="left", padx=8)
        cb.pack(side="left", padx=10)
        ttk.Button(pick, text="Afficher", command=show).pack(side="left")
        cb.bind("<<ComboboxSelected>>", show)
        fill()
        if st.get("id") in ids:
            cb.current(ids.index(st["id"])); show()

    # ---------- onglet "Espace d'impression" : listes a cocher + PDF ----------
    def build_print(self, f):
        tk.Label(f, text="\U0001F5A8  Espace d'impression :", bg=TT_BLUE, fg="white", font=("Segoe UI", 16, "bold"),
                 anchor="w", padx=14, pady=8).pack(fill="x")
        body = tk.Frame(f); body.pack(expand=True, fill="y", pady=14)
        body.rowconfigure(1, weight=1)
        self._pw_cvs = []
        for c, (titre, kind) in enumerate((("Groupes", "grp"), ("Formateurs", "frm"), ("Espaces", "esp"))):
            body.columnconfigure(c, pad=20)
            tk.Label(body, text=titre + " :", anchor="w").grid(row=0, column=c, sticky="w", padx=14, pady=(0, 6))
            box = tk.Frame(body, bd=1, relief="solid", bg="white"); box.grid(row=1, column=c, padx=14, sticky="ns")
            cv = tk.Canvas(box, width=300, height=420, bg="white", highlightthickness=0)
            sb = ttk.Scrollbar(box, orient="vertical", command=cv.yview); cv.configure(yscrollcommand=sb.set)
            sb.pack(side="right", fill="y"); cv.pack(side="left", fill="both", expand=True)
            inner = tk.Frame(cv, bg="white"); cv.create_window((0, 0), window=inner, anchor="nw", width=285)
            inner.bind("<Configure>", lambda e, cv=cv: cv.configure(scrollregion=cv.bbox("all")))
            self._pw_cvs.append(cv)
            vars_ = []
            for n, (i, lab) in enumerate(self.list_items(kind)):
                bg = "#f3f3f3" if n % 2 else "white"
                v = self.psel.setdefault(f"{kind}:{i}", tk.BooleanVar(self, value=False)); vars_.append(v)
                tk.Checkbutton(inner, text=lab, variable=v, anchor="w", bg=bg, activebackground=bg, bd=0,
                               highlightthickness=0, padx=6, pady=2).pack(fill="x")
            bt = tk.Frame(body); bt.grid(row=2, column=c, pady=12)
            ttk.Button(bt, text="+", width=4, command=lambda vs=vars_: [v.set(True) for v in vs]).pack(side="left", padx=14)
            ttk.Button(bt, text="\u2212", width=4, command=lambda vs=vars_: [v.set(False) for v in vs]).pack(side="left", padx=14)
        ttk.Button(body, text="Imprimer", command=self.print_selection).grid(row=3, column=1, sticky="ew", padx=14, pady=4, ipady=4)
        if not getattr(self, "_pw_bound", False):          # molette : fait defiler la liste sous le pointeur
            self._pw_bound = True
            self.winfo_toplevel().bind_all("<MouseWheel>", self._print_wheel, add="+")

    def _print_wheel(self, e):
        for cv in self._pw_cvs:
            try:
                if cv.winfo_exists() and cv.winfo_rootx() <= e.x_root < cv.winfo_rootx() + cv.winfo_width() \
                        and cv.winfo_rooty() <= e.y_root < cv.winfo_rooty() + cv.winfo_height():
                    cv.yview_scroll(int(-e.delta / 120), "units"); return
            except tk.TclError:
                pass

    def print_selection(self):
        """Genere un PDF (une page par emploi coche) et l'ouvre pour impression / enregistrement."""
        items = []
        for kind in ("grp", "frm", "esp"):
            for i, _ in self.list_items(kind):
                v = self.psel.get(f"{kind}:{i}")
                if v is not None and v.get(): items.append((kind, i))
        if not items:
            return messagebox.showinfo("Imprimer", "Cochez au moins un groupe, un formateur ou un espace.")
        try:
            pdf = tt_pdf_emploi(self.D, items)
        except Exception as ex:
            logger.exception("Erreur de generation du PDF des emplois du temps")
            return messagebox.showerror("Imprimer", f"Impossible de générer le PDF : {ex}")
        self.winfo_toplevel().open_pdf_viewer(pdf, f"emplois_du_temps_{datetime.now():%Y%m%d_%H%M%S}.pdf",
                                              f"Les emplois du temps ({len(items)} page(s))")

    # ---------- accueil ----------
    def build_home(self, f):
        c = tk.Canvas(f, bg="#f4f4f4", highlightthickness=0); c.pack(fill="both", expand=True)
        c.bind("<Configure>", lambda e: self.draw_home(c))

    def draw_home(self, c):
        c.delete("all"); D = self.D; W, H = max(c.winfo_width(), 600), max(c.winfo_height(), 420)
        c.create_rectangle(10, 10, W - 10, 54, fill=TT_BLUE if self.mode == "directeur" else "#0e7c66", width=0)
        c.create_text(24, 32, anchor="w", fill="white", font=("Segoe UI", 15, "bold"),
                      text=self.mode_label() + "   —   Tableau de bord : " + D["file"])
        hrs = {e["id"]: sum(s["dur"] for s in D["seances"] if s["espace"] == e["id"]) / 4 for e in D["espaces"]}
        cap = len(D["espaces"]) * 60; taux = sum(hrs.values()) / cap * 100 if cap else 0
        kp = [(len(D["formateurs"]), "Formateurs", TT_GREEN), (len(D["groupes"]), "Groupes", TT_BLUE), (len(D["espaces"]), "Espaces", TT_GREY),
              (len(D["seances"]), "Séances", TT_ORANGE), (f"{taux:.1f}%", "Taux d'occupation", TT_ORANGE)]
        bw = (W - 20 - 56) / 5
        for i, (v, l, col) in enumerate(kp):
            x = 10 + i * (bw + 14)
            c.create_rectangle(x, 70, x + bw, 170, fill=col, width=0)
            c.create_text(x + bw / 2, 108, text=str(v), fill="white", font=("Segoe UI", 28, "bold"))
            c.create_text(x + bw / 2, 150, text=l, fill="white", font=("Segoe UI", 11, "bold"))
        c.create_text(W / 2, 200, text="Occupation des espaces (heures/semaine)", font=("Segoe UI", 12))
        top, bot, left = 225, H - 60, 50
        mx = max(10, math.ceil(max(hrs.values(), default=0) / 5) * 5)
        c.create_line(left, top, left, bot); c.create_line(left, bot, W - 20, bot)
        c.create_text(left - 6, top, text=str(mx), anchor="e"); c.create_text(left - 6, bot, text="0", anchor="e")
        if hrs:
            step = (W - 20 - left) / len(hrs)
            for i, (eid, v) in enumerate(hrs.items()):
                x = left + i * step + step * .1; y = bot - (bot - top) * v / mx
                c.create_rectangle(x, y, x + step * .8, bot, fill=TT_ORANGE, width=0)
                c.create_text(x + step * .4, y - 8, text=f"{v:g}")
                c.create_text(x + step * .4, bot + 6, anchor="n", width=step * .9, justify="center", font=("Segoe UI", 8),
                              text=tt_get(D, "espaces", eid)["nom"])

    # ---------- etablissement ----------
    def build_etab(self, f):
        tk.Label(f, text="Etablissement", bg=TT_GREEN, fg="white", font=("Segoe UI", 16, "bold"), anchor="w", padx=12, pady=6).pack(fill="x", padx=10, pady=8)
        form = ttk.Frame(f); form.pack(fill="x", padx=10); form.columnconfigure(1, weight=1); V = {}
        for r, (k, lab) in enumerate(TT_ETAB):
            ttk.Label(form, text=lab + " :").grid(row=r, column=0, sticky="w", pady=5)
            V[k] = tk.StringVar(value=self.D["etab"].get(k, "")); ttk.Entry(form, textvariable=V[k]).grid(row=r, column=1, sticky="ew", padx=10)
        def ok():
            self.D["etab"] = {k: v.get().strip() for k, v in V.items()}; messagebox.showinfo("Etablissement", "Enregistré."); self.autosave()
        ttk.Button(f, text="Enregistrer", command=ok).pack(side="right", padx=10, pady=10)

    # ---------- listes (formateurs, filieres, groupes, espaces) ----------
    def build_crud(self, f, k):
        title, color, fields = TT_SCHEMA[k]; D = self.D
        if k == "formateurs": self.sync_formateurs()
        tk.Label(f, text=title, bg=color, fg="white", font=("Segoe UI", 16, "bold"), anchor="w", padx=12, pady=6).pack(fill="x", padx=10, pady=8)
        fl = [(x["id"], f"{x['abrev']} - {x['nom']}" if x.get("abrev") else x["nom"]) for x in D["filieres"]]
        form = ttk.Frame(f); form.pack(fill="x", padx=10); form.columnconfigure(1, weight=1); V, W, ed = {}, {}, [None]
        for r, (key, lab, opt) in enumerate(fields):
            ttk.Label(form, text=lab + " :").grid(row=r, column=0, sticky="w", pady=4); V[key] = tk.StringVar()
            if opt:
                W[key] = ttk.Combobox(form, textvariable=V[key], state="readonly", values=[l for _, l in fl] if opt == "@f" else opt)
            else: W[key] = ttk.Entry(form, textvariable=V[key])
            W[key].grid(row=r, column=1, sticky="ew", padx=10)

        def reset():
            ed[0] = None
            for key, lab, opt in fields:
                V[key].set(""); 
                if opt and W[key]["values"]: W[key].current(0)
        reset()
        def sauver():
            d = {}
            for key, lab, opt in fields:
                v = V[key].get().strip()
                if opt == "@f": v = next((i for i, l in fl if l == v), None)
                d[key] = v
            if not d["nom"]: return messagebox.showwarning("Time Table", "Le nom est obligatoire.")
            if k == "groupes" and d["filiere"] is None: return messagebox.showwarning("Time Table", "Ajoute d'abord une filière.")
            if ed[0]: tt_get(D, k, ed[0]).update(d)
            else: d["id"] = self.uid(); D[k].append(d)
            self.refresh()
        bt = ttk.Frame(f); bt.pack(fill="x", padx=10, pady=8)
        ttk.Button(bt, text="Annuler", command=reset).pack(side="right", padx=4)
        ttk.Button(bt, text="Enregistrer", command=sauver).pack(side="right")
        if k == "formateurs":
            nb_p = sum(1 for x in D[k] if x.get("type") == "Permanent")
            ttk.Label(bt, text=f"{nb_p} permanent(s)  ·  {len(D[k]) - nb_p} vacataire(s)").pack(side="left")
            ttk.Button(bt, text="Recharger Personnel / Vacataires", command=lambda: (self.sync_formateurs(True), self.refresh())).pack(side="left", padx=10)

        tv = ttk.Treeview(f, columns=[x[0] for x in fields], show="headings", selectmode="browse", height=14)
        for key, lab, opt in fields: tv.heading(key, text=lab); tv.column(key, width=150)
        for x in D[k]:
            tv.insert("", "end", iid=str(x["id"]), values=[dict(fl).get(x[key], "?") if opt == "@f" else x.get(key, "") for key, _, opt in fields])
        tv.pack(fill="both", expand=True, padx=10)
        def modifier(*_):
            if not tv.selection(): return
            x = tt_get(D, k, int(tv.selection()[0])); ed[0] = x["id"]
            for key, lab, opt in fields: V[key].set(dict(fl).get(x[key], "") if opt == "@f" else x.get(key, ""))
        def supprimer():
            msg = ("Retirer ce formateur de l'emploi du temps (avec ses séances) ?\nSa fiche Personnel / Vacataire n'est pas supprimée."
                   if k == "formateurs" else "Supprimer cet élément et ses séances ?")
            if tv.selection() and messagebox.askyesno("Supprimer", msg):
                self.delete(k, int(tv.selection()[0]))
        tv.bind("<Double-Button-1>", modifier)
        b2 = ttk.Frame(f); b2.pack(fill="x", padx=10, pady=8)
        ttk.Button(b2, text="Modifier", command=modifier).pack(side="left"); ttk.Button(b2, text="Supprimer", command=supprimer).pack(side="left", padx=6)

    def delete(self, k, i):
        D = self.D
        if k == "formateurs":
            x = tt_get(D, k, i)
            if x and x.get("src"): D.setdefault("fmt_ignores", []).append(x["src"])
        if k == "filieres":
            gs = [g["id"] for g in D["groupes"] if g["filiere"] == i]
            D["groupes"] = [g for g in D["groupes"] if g["filiere"] != i]; D["seances"] = [s for s in D["seances"] if s["groupe"] not in gs]
        else:
            fld = {"groupes": "groupe", "espaces": "espace", "formateurs": "formateur"}[k]
            D["seances"] = [s for s in D["seances"] if s[fld] != i]
        D[k] = [x for x in D[k] if x["id"] != i]; self.refresh()

    # ---------- emploi du temps (espace / groupe / formateur) ----------
    def build_tt(self, f, key, ck=None):
        ck = ck or key          # cle du canvas (permet d'afficher un emploi dans l'onglet "Emploi")
        D = self.D; kind, i = key.split(":"); i = int(i); coll, fld, lab, col = TT_KIND[kind]; o = tt_get(D, coll, i)
        lst = [s for s in D["seances"] if s[fld] == i]
        bar = tk.Frame(f, bg=col); bar.pack(fill="x", padx=6, pady=6)
        ICO = {"frm": "\U0001F464", "grp": "\U0001F465", "esp": "\U0001F3E0"}
        tk.Label(bar, text=f"{ICO.get(kind, '')}   {lab} : {tt_fname(o) if kind == 'frm' else o['nom']}", bg=col, fg="white", font=("Segoe UI", 16, "bold"), padx=14, pady=8).pack(side="left")
        m = sum(s["dur"] for s in lst) * 15
        tk.Label(bar, text=f"{m // 60:02d} H {m % 60:02d} Min",
                 bg=col, fg="white", font=("Segoe UI", 16, "bold"), padx=14).pack(side="right")
        if kind == "frm":                                       # semaine affichee : les jours d'absence du formateur sont grises
            if getattr(self, "sem_abs", None) is None:
                self.sem_abs = self.abs_first_week(i)           # 1re ouverture : semaine de la prochaine absence
            wk = tk.Frame(bar, bg=col); wk.pack(side="right", padx=10)
            info_abs = tk.Label(wk, bg=col, fg="#ffe9a8", font=("Segoe UI", 10, "bold")); info_abs.pack(side="left", padx=(0, 12))
            tk.Label(wk, text="Semaine du :", bg=col, fg="white", font=("Segoe UI", 10)).pack(side="left", padx=(0, 6))
            cw_ = DateEntry(wk, date_pattern="dd/mm/yyyy", width=11, background=MAIN_COLOR, foreground="white", borderwidth=2)
            cw_.set_date(self.sem_lundi())
            def go(delta=0, *_):
                d0 = self.sem_lundi() + timedelta(days=7 * delta) if delta else cw_.get_date()
                self.sem_abs = d0; cw_.set_date(self.sem_lundi())
                ad = self.abs_days(i)
                info_abs.config(text=("Absent : " + ", ".join(f"{TT_DAYS[d][:3]}. ({m})" for d, m in sorted(ad.items()))) if ad else "Aucune absence cette semaine")
                self.draw(cv, kind, lst, ad)
                refresh_mini()
            tk.Button(wk, text="\u25C0", command=lambda: go(-1), relief="flat", bg="#ffffff", fg=col, bd=0, padx=8, cursor="hand2").pack(side="left")
            cw_.pack(side="left", padx=3)
            tk.Button(wk, text="\u25B6", command=lambda: go(1), relief="flat", bg="#ffffff", fg=col, bd=0, padx=8, cursor="hand2").pack(side="left")
            cw_.bind("<<DateEntrySelected>>", lambda e: go(0))
            ad0 = self.abs_days(i)
            info_abs.config(text=("Absent : " + ", ".join(f"{TT_DAYS[d][:3]}. ({m})" for d, m in sorted(ad0.items()))) if ad0 else "Aucune absence cette semaine")
        body = ttk.Frame(f); body.pack(fill="both", expand=True, padx=6)
        W, Ht = TT_LW + TT_Q * TT_QW + 4, TT_HH + 6 * TT_RH + 4
        left = ttk.Frame(body)                                  # grille principale + emplois reduits (formateur / groupe / salle)
        cv = tk.Canvas(left, bg="white", highlightthickness=0, height=Ht, scrollregion=(0, 0, W, Ht)); self.canv[ck] = cv
        # Panneau de droite : 1re case = elements a glisser dans la grille, 2e case = element a selectionner
        #   groupe   -> formateurs (glisser) + salles/ateliers (selectionner)
        #   formateur-> groupes (glisser)    + salles/ateliers (selectionner)
        #   espace   -> groupes (glisser)    + formateurs (selectionner)
        side = ttk.Frame(body); side.pack(side="right", fill="y", padx=(8, 0))
        D_k, S_k = {"grp": ("f", "e"), "frm": ("g", "e"), "esp": ("g", "f")}[kind]
        COLL = {"g": ("groupes", "Groupes"), "f": ("formateurs", "Formateurs"), "e": ("espaces", "Salles / Ateliers")}
        nm = lambda k, x: tt_fname(x) if k == "f" else x["nom"]
        KMAP = {"g": "grp", "f": "frm", "e": "esp"}; ATTR = {"g": "sel_g", "f": "sel_f", "e": "sel_e"}
        def mk_list(k, titre, h, pad):
            bgc = TT_GREY if k == "e" else TT_BLUE                  # espaces = gris, groupes / formateurs = bleu
            tk.Label(side, text="\u25BC  " + titre, bg="#eef1f5", fg="#33475b", anchor="w", font=("Segoe UI", 10),
                     padx=8, pady=3).pack(fill="x", pady=(pad, 0))
            lb = tk.Listbox(side, exportselection=False, height=h, width=26, font=("Segoe UI", 11), activestyle="none", relief="flat",
                            bg=bgc, fg="white", highlightthickness=4, highlightbackground="#ffffff", highlightcolor="#ffffff",
                            selectbackground="#e8a020", selectforeground="white", bd=0)
            lb.pack(fill="x")
            for x in D[COLL[k][0]]: lb.insert("end", "   " + nm(k, x))
            return lb
        # case a glisser
        items = D[COLL[D_k][0]]
        lg = mk_list(D_k, f"{COLL[D_k][1]}  (glisse dans la grille)", 11, 0)
        def lg_press(e):
            n = lg.nearest(e.y)
            if 0 <= n < len(items):
                self.drag = {"k": D_k, "id": items[n]["id"], "dur": 4}
                setattr(self, ATTR[D_k], items[n]["id"]); refresh_mini()
        lg.bind("<ButtonPress-1>", lg_press)
        lg.bind("<B1-Motion>", lambda e: self.preview(cv, key, *self.ptr(cv)))
        lg.bind("<ButtonRelease-1>", lambda e: self.g_drop(cv, key))
        for n, x in enumerate(items):
            if x["id"] == getattr(self, ATTR[D_k]): lg.selection_set(n)
        # case a selectionner
        sitems = D[COLL[S_k][0]]
        ls = mk_list(S_k, f"{COLL[S_k][1]}  (sélectionne)", 11, 10)
        attr = ATTR[S_k]
        if S_k == "e" and sitems and getattr(self, attr) not in [x["id"] for x in sitems]:
            setattr(self, attr, sitems[0]["id"])                 # par defaut : premiere salle
        for n, x in enumerate(sitems):
            if x["id"] == getattr(self, attr): ls.selection_set(n)
        def ls_sel(e):
            if ls.curselection():
                setattr(self, attr, sitems[ls.curselection()[0]]["id"]); refresh_mini()
        ls.bind("<<ListboxSelect>>", ls_sel)

        # Sous la grille : emplois (lecture seule) des deux elements choisis a droite -> libre ou occupe ?
        left.pack(side="left", fill="both", expand=True)
        hs = ttk.Scrollbar(left, orient="horizontal", command=cv.xview); cv.configure(xscrollcommand=hs.set)
        cv.pack(side="top", fill="x"); hs.pack(side="top", fill="x")
        mini = ttk.Frame(left); mini.pack(side="top", fill="both", expand=True, pady=(8, 0))
        minis = []
        for k in (D_k, S_k):
            box = tk.Frame(mini, bg="white", highlightthickness=1, highlightbackground="#c9d4e0")
            box.pack(side="left", fill="both", expand=True, padx=(0, 6))
            ttl = tk.Label(box, anchor="w", font=("Segoe UI", 12, "bold"), fg="white", padx=14, pady=6); ttl.pack(fill="x")
            mc = tk.Canvas(box, bg="white", highlightthickness=0, height=300); mc.pack(fill="both", expand=True)
            mc.bind("<Configure>", lambda e: refresh_mini())
            mc.bind("<MouseWheel>", lambda e, mc=mc: mc.yview_scroll(int(-e.delta / 120), "units"))
            minis.append((k, ttl, mc))
        def refresh_mini():
            for k, ttl, mc in minis:
                coll, fld, lab, col = TT_KIND[KMAP[k]]
                iid = getattr(self, ATTR[k]); o = tt_get(D, coll, iid) if iid is not None else None
                ttl.configure(bg=col)
                if o is None:
                    ttl.configure(text=f"{ICO.get(KMAP[k], '')}   {lab} :"); mc.delete("all")
                    mc.create_text(10, 12, anchor="nw", fill="#6b7a89", width=380,
                                   text=f"Clique sur un élément de la liste de droite pour voir son emploi et savoir s'il est libre.")
                    continue
                l2 = [x for x in D["seances"] if x[fld] == iid]; m2 = sum(x["dur"] for x in l2) * 15
                ttl.configure(text=f"{ICO.get(KMAP[k], '')}   {lab} : {nm(k, o)}   —   {m2 // 60:02d} H {m2 % 60:02d} Min")
                self.draw_mini(mc, KMAP[k], l2, max(mc.winfo_width(), 420), self.abs_days(iid) if KMAP[k] == "frm" else None)
        refresh_mini()
        cv.bind("<ButtonPress-1>", lambda e: self.press(e, key, ck)); cv.bind("<B1-Motion>", lambda e: self.motion(e, key, ck))
        cv.bind("<ButtonRelease-1>", lambda e: self.release(e, key, ck)); self.draw(cv, kind, lst, self.abs_days(i) if kind == "frm" else None)

    def draw(self, cv, kind, lst, absd=None):
        D = self.D; cv.delete("all"); absd = absd or {}
        cv.create_rectangle(TT_LW, 0, TT_LW + 2 * TT_QW, TT_HH, width=2); cv.create_text(TT_LW + TT_QW, TT_HH / 2, text=f"{tt_qt(0)} - {tt_qt(2)}", font=("Segoe UI", 7))
        for n in range(10):
            x = TT_LW + (2 + 4 * n) * TT_QW; cv.create_rectangle(x, 0, x + 4 * TT_QW, TT_HH, width=2)
            cv.create_text(x + 2 * TT_QW, TT_HH / 2, text=f"{tt_qt(2 + 4 * n)} - {tt_qt(6 + 4 * n)}", font=("Segoe UI", 9))
        for d, name in enumerate(TT_DAYS):
            y = TT_HH + d * TT_RH
            if d in absd:                                       # jour d'absence : toute la ligne en gris
                cv.create_rectangle(0, y, TT_LW + TT_Q * TT_QW, y + TT_RH, fill="#c9ced4", outline="")
            cv.create_rectangle(0, y, TT_LW, y + TT_RH, width=2); cv.create_text(8, y + TT_RH / 2 - (8 if d in absd else 0), anchor="w", text=name, font=("Segoe UI", 14))
            if d in absd:
                cv.create_text(8, y + TT_RH / 2 + 12, anchor="w", text=str(absd[d])[:22], fill="#b3261e", font=("Segoe UI", 8, "bold"))
                cv.create_text(TT_LW + TT_Q * TT_QW / 2, y + TT_RH / 2, text=f"ABSENT  —  {absd[d]}", fill="#6b7480", font=("Segoe UI", 13, "bold"))
            for q in range(TT_Q + 1):
                x = TT_LW + q * TT_QW; hour = q == 0 or q % 4 == 2
                cv.create_line(x, y, x, y + TT_RH, width=4 if q == 22 else (2 if hour else 1), dash=() if hour else (3, 3), fill="black" if hour else "#999")
            cv.create_line(TT_LW, y, TT_LW + TT_Q * TT_QW, y, width=1)
        cv.create_line(TT_LW, TT_HH + 6 * TT_RH, TT_LW + TT_Q * TT_QW, TT_HH + 6 * TT_RH, width=2)
        cv.create_rectangle(1, TT_HH, TT_LW + TT_Q * TT_QW, TT_HH + 6 * TT_RH, width=3)         # cadre epais autour des jours
        for s in lst:
            txt = tt_seance_text(D, s, kind)
            col = tt_color(D, s.get("espace"))
            x1, y1 = TT_LW + s["start"] * TT_QW + 2, TT_HH + s["day"] * TT_RH + 2; x2, y2 = x1 + s["dur"] * TT_QW - 4, y1 + TT_RH - 4
            cv.create_rectangle(x1, y1, x2, y2, fill=col, outline="#d32f2f" if s["day"] in absd else col, width=3 if s["day"] in absd else 1, tags=("ses", f"s{s['id']}"))
            cv.create_text((x1 + x2) / 2, (y1 + y2) / 2, text=txt, fill="white", width=max(x2 - x1 - 6, 20), justify="center",
                           font=("Segoe UI", 9, "bold"), tags=("ses", f"s{s['id']}"))

    def draw_mini(self, cv, kind, lst, W, absd=None):
        """Version agrandie (lecture seule) d'une grille d'emploi : permet de voir si un formateur / groupe / salle est libre.
        Les lignes occupent toute la hauteur disponible ; les seances qui se chevauchent ont des couloirs separes."""
        import tkinter.font as tkfont
        D = self.D; cv.delete("all"); absd = absd or {}
        lw, hh = 92, 26
        H = cv.winfo_height()
        if H < 80: H = int(float(cv.cget("height")))        # pas encore affiche : hauteur demandee
        qw = max((W - lw - 4) / TT_Q, 8)
        if not hasattr(self, "_mini_fonts"): self._mini_fonts = {}

        def fit(txt, mw, f):
            txt = str(txt or "")
            if mw <= 10: return ""
            if f.measure(txt) <= mw: return txt
            while txt and f.measure(txt + "…") > mw: txt = txt[:-1]
            return (txt.rstrip() + "…") if txt else ""

        def nm(coll, i, fmt=lambda o: o["nom"]):
            try: o = tt_get(D, coll, i) if i is not None else None
            except Exception: o = None
            return fmt(o) if o else "?"

        # une ligne par jour ; plusieurs couloirs si des seances se chevauchent
        layout = []                                     # (jour, couloir, seance)
        nb_cou = [1] * len(TT_DAYS)
        for d in range(len(TT_DAYS)):
            fins = []
            for s in sorted((x for x in lst if x["day"] == d), key=lambda x: x["start"]):
                c = next((i for i, e in enumerate(fins) if e <= s["start"]), None)
                if c is None: fins.append(0); c = len(fins) - 1
                fins[c] = s["start"] + s["dur"]; layout.append((d, c, s))
            nb_cou[d] = max(1, len(fins))
        lh = max(30, min(80, (H - hh - 4) // sum(nb_cou)))          # tout tient dans la hauteur disponible (6 jours)
        fs = 10 if lh >= 46 else 9 if lh >= 38 else 8              # taille du texte selon la hauteur des lignes
        if fs not in self._mini_fonts:
            self._mini_fonts[fs] = (tkfont.Font(root=cv, family="Segoe UI", size=fs, weight="bold"),
                                    tkfont.Font(root=cv, family="Segoe UI", size=fs - 1))
        fb, fn = self._mini_fonts[fs]
        ytop, y = [], hh
        for d in range(len(TT_DAYS)): ytop.append(y); y += nb_cou[d] * lh
        total = y + 2

        # entete des heures
        cv.create_rectangle(lw, 0, lw + 2 * qw, hh, outline="#555"); cv.create_text(lw + qw, hh / 2, text=tt_qt(0), font=("Segoe UI", 8))
        for n in range(10):
            x = lw + (2 + 4 * n) * qw
            cv.create_rectangle(x, 0, x + 4 * qw, hh, outline="#555"); cv.create_text(x + 2 * qw, hh / 2, text=tt_qt(2 + 4 * n), font=("Segoe UI", 10))
        # lignes des jours
        for d, name in enumerate(TT_DAYS):
            y0, rh = ytop[d], nb_cou[d] * lh
            cv.create_rectangle(0, y0, lw, y0 + rh, outline="#555"); cv.create_text(8, y0 + min(rh, lh) / 2, anchor="w", text=name, font=("Segoe UI", 10))
            cv.create_rectangle(lw, y0, lw + TT_Q * qw, y0 + rh, outline="#555", fill="#c9ced4" if d in absd else "")
            if d in absd:
                cv.create_text(lw + TT_Q * qw / 2, y0 + rh / 2, text=f"ABSENT  —  {absd[d]}", fill="#6b7480", font=("Segoe UI", 10, "bold"))
            for q in [2 + 4 * n for n in range(10)]:
                cv.create_line(lw + q * qw, y0, lw + q * qw, y0 + rh, fill="#bbb")
        # seances
        for d, c, s in layout:
            col = tt_color(D, s.get("espace"))
            x1, y1 = lw + s["start"] * qw + 1, ytop[d] + c * lh + 1; x2, y2 = x1 + s["dur"] * qw - 2, y1 + lh - 2
            cv.create_rectangle(x1, y1, x2, y2, fill=col, outline="white")
            g = nm("groupes", s.get("groupe")); e = nm("espaces", s.get("espace"))
            f = nm("formateurs", s.get("formateur"), tt_fname)
            a, b = {"frm": (g, e), "esp": (g, f), "grp": (f, e)}.get(kind, (g, ""))
            mw = x2 - x1 - 8
            if mw >= 150:      # case large : "A · B" puis le module
                l1, l2 = f"{a} · {b}", s.get("matiere", "")
            else:              # case etroite : un element par ligne (plus lisible que du texte coupe)
                l1, l2 = a, b
            cv.create_text(x1 + 4, y1 + (lh - 2) * 0.30, anchor="w", fill="white", font=fb, text=fit(l1, mw, fb))
            cv.create_text(x1 + 4, y1 + (lh - 2) * 0.72, anchor="w", fill="white", font=fn, text=fit(l2, mw, fn))
        cv.configure(scrollregion=(0, 0, W, max(total, H)))
        cv.yview_moveto(0)

    def ptr(self, cv):
        return cv.canvasx(cv.winfo_pointerx() - cv.winfo_rootx()), cv.canvasy(cv.winfo_pointery() - cv.winfo_rooty())

    def target(self, x, y, d):
        day = int((y - TT_HH) // TT_RH)
        if not 0 <= day < 6: return None
        q = round((x - d.get("off", 0) - TT_LW) / TT_QW) if d["k"] == "s" else int((x - TT_LW) // TT_QW)
        return day, max(0, min(q, TT_Q - d["dur"]))

    def preview(self, cv, key, x, y):
        cv.delete("ov"); d = self.drag; t = d and self.target(x, y, d)
        if t:
            x1 = TT_LW + t[1] * TT_QW; y1 = TT_HH + t[0] * TT_RH
            bad = key.startswith("frm:") and t[0] in self.abs_days(int(key.split(":")[1]))
            cv.create_rectangle(x1, y1, x1 + d["dur"] * TT_QW, y1 + TT_RH, fill="#e53935" if bad else "#06c26a", stipple="gray50",
                                outline="#b3261e" if bad else "#068a4e", width=2, tags="ov")

    def press(self, e, key, ck=None):
        cv = self.canv[ck or key]; x, y = cv.canvasx(e.x), cv.canvasy(e.y)
        hit = [t for i in cv.find_overlapping(x, y, x, y) for t in cv.gettags(i) if t[0] == "s" and t[1:].isdigit()]
        if hit:
            s = tt_get(self.D, "seances", int(hit[-1][1:]))
            self.drag = {"k": "s", "id": s["id"], "dur": s["dur"], "off": x - (TT_LW + s["start"] * TT_QW), "moved": False, "x0": e.x, "y0": e.y}
        else: self.drag = {"k": "c", "dur": 4}

    def motion(self, e, key, ck=None):
        d = self.drag
        if d and d["k"] == "s":
            if abs(e.x - d["x0"]) + abs(e.y - d["y0"]) > 5: d["moved"] = True
            if d["moved"]: self.preview(self.canv[ck or key], key, *self.ptr(self.canv[ck or key]))

    def release(self, e, key, ck=None):
        cv = self.canv[ck or key]; cv.delete("ov"); d, self.drag = self.drag, None
        if not d: return
        x, y = cv.canvasx(e.x), cv.canvasy(e.y); t = self.target(x, y, d)
        if d["k"] == "c":
            if t:
                n0 = self.new_s(key, *t)
                if self.abs_ok(n0.get("formateur"), n0["day"]): self.dialog(n0, True)
        elif not d["moved"]: self.dialog(tt_get(self.D, "seances", d["id"]), False)
        elif t:
            s = tt_get(self.D, "seances", d["id"]); n = dict(s, day=t[0], start=t[1]); m = tt_conflict(self.D, n)
            if m: messagebox.showwarning("Conflit", m)
            elif self.abs_ok(n.get("formateur"), n["day"]): s.update(n); self.refresh()

    def g_drop(self, cv, key):
        cv.delete("ov"); d, self.drag = self.drag, None
        if not d: return
        W, H = cv.winfo_width(), cv.winfo_height(); px, py = cv.winfo_pointerx() - cv.winfo_rootx(), cv.winfo_pointery() - cv.winfo_rooty()
        if not (0 <= px <= W and 0 <= py <= H): return
        t = self.target(cv.canvasx(px), cv.canvasy(py), d)
        if not t: return
        kind, kid = key.split(":"); kid = int(kid)
        esp_def = self.sel_e if self.sel_e is not None else (self.D["espaces"][0]["id"] if self.D["espaces"] else 0)
        s = {"id": self.uid(), "groupe": 0, "espace": esp_def, "formateur": self.sel_f, "day": t[0], "start": t[1], "dur": 4}
        if kind == "esp":   s.update(espace=kid, groupe=d["id"])                    # formateur = celui selectionne
        elif kind == "frm": s.update(formateur=kid, groupe=d["id"])                 # espace = celui selectionne
        else:               s.update(groupe=kid, formateur=d["id"])                 # groupe : formateur glisse, espace selectionne
        m = tt_conflict(self.D, s)
        if m: messagebox.showwarning("Conflit", m)
        elif self.abs_ok(s.get("formateur"), s["day"]): self.D["seances"].append(s); self.refresh()

    def new_s(self, key, day, q):
        D = self.D; kind, i = key.split(":"); i = int(i)
        s = {"id": self.uid(), "groupe": D["groupes"][0]["id"] if D["groupes"] else 0, "espace": D["espaces"][0]["id"] if D["espaces"] else 0,
             "formateur": self.sel_f, "day": day, "start": q, "dur": 4}
        s[TT_KIND[kind][1]] = i
        return s

    def dialog(self, s, new):
        D = self.D; gs, es, fs = D["groupes"], D["espaces"], D["formateurs"]
        if not gs or not es: return messagebox.showinfo("Time Table", "Ajoute d'abord au moins un groupe et un espace.")
        t = tk.Toplevel(self); t.title("Séance"); t.transient(self.winfo_toplevel()); t.after(150, t.grab_set)
        t.configure(bg="#f4f6f9")
        tk.Label(t, text="Détail de la séance", bg="#0056b3", fg="white",
                 font=("Segoe UI", 12, "bold"), anchor="w", padx=12, pady=8).grid(row=0, column=0, columnspan=2, sticky="ew")
        tk.Frame(t, height=2, bg="#e8a020").grid(row=1, column=0, columnspan=2, sticky="ew")
        ix = lambda l, i: next((n for n, x in enumerate(l) if x["id"] == i), 0)
        def combo(r, lab, items, idx):
            ttk.Label(t, text=lab).grid(row=r + 2, column=0, sticky="w", padx=12, pady=4)
            c = ttk.Combobox(t, values=items, state="readonly", width=34); c.grid(row=r + 2, column=1, padx=12)
            if items: c.current(max(0, min(idx, len(items) - 1)))
            return c
        cg = combo(0, "Groupe", [g["nom"] for g in gs], ix(gs, s["groupe"])); ce = combo(1, "Espace", [e["nom"] for e in es], ix(es, s["espace"]))
        cf = combo(2, "Formateur", ["-"], 0)
        cd = combo(3, "Jour", TT_DAYS, s["day"]); cs = combo(4, "Début", [tt_qt(q) for q in range(TT_Q)], s["start"])
        cu = combo(5, "Durée", [tt_dur_txt(q) for q in range(1, TT_Q + 1)], s["dur"] - 1)
        ttk.Label(t, text="Semaine du").grid(row=8, column=0, sticky="w", padx=12, pady=4)
        cw = DateEntry(t, date_pattern="dd/mm/yyyy", width=12, background=MAIN_COLOR, foreground="white", borderwidth=2)
        cw.grid(row=8, column=1, sticky="w", padx=12)
        note = ttk.Label(t, text="", foreground="#a83232", wraplength=300, justify="left")
        note.grid(row=9, column=0, columnspan=2, sticky="w", padx=12)
        avail = []                                  # formateurs proposes (absents du jour exclus)

        def refresh_f(*_):
            sel = avail[cf.current() - 1]["id"] if cf.current() > 0 and avail else s["formateur"]
            jour = cw.get_date() - timedelta(days=cw.get_date().weekday()) + timedelta(days=cd.current())
            absents = tt_absents(jour)
            avail[:] = [x for x in fs if not ({tt_norm(tt_fname(x)), tt_norm(f"{x.get('prenom', '')} {x['nom']}")} & absents)]
            hors = [tt_fname(x) for x in fs if x not in avail]
            cf["values"] = ["-"] + [tt_fname(x) for x in avail]
            pos = next((n + 1 for n, x in enumerate(avail) if x["id"] == sel), 0)
            cf.current(pos)
            note.config(text=("Absent(s) le " + jour.strftime("%d/%m/%Y") + " (absence) : " + ", ".join(hors)) if hors else "")
        cd.bind("<<ComboboxSelected>>", refresh_f); cw.bind("<<DateEntrySelected>>", refresh_f)
        refresh_f()

        def ok():
            n = dict(s, groupe=gs[cg.current()]["id"], espace=es[ce.current()]["id"], formateur=avail[cf.current() - 1]["id"] if cf.current() > 0 else None,
                     day=cd.current(), start=cs.current(), dur=cu.current() + 1)
            m = tt_conflict(D, n)
            if m: return messagebox.showwarning("Conflit", m, parent=t)
            if new: D["seances"].append(n)
            else: s.update(n)
            t.destroy(); self.refresh()
        def rm(): D["seances"].remove(s); t.destroy(); self.refresh()
        b = ttk.Frame(t); b.grid(row=10, column=0, columnspan=2, pady=12)
        ttk.Button(b, text="Enregistrer", command=ok).pack(side="left", padx=4)
        if not new: ttk.Button(b, text="Supprimer", command=rm).pack(side="left", padx=4)
        ttk.Button(b, text="Annuler", command=t.destroy).pack(side="left", padx=4)

    # ---------- couleurs des salles / ateliers ----------
    def couleurs_dialog(self):
        """Choisir la couleur de chaque salle/atelier (clic sur un carre de couleur)."""
        D = self.D
        CHOIX = TT_PALETTE + ["#8e99a4", "#33475b", "#000000"]
        t = tk.Toplevel(self); t.title("Couleurs des salles et ateliers")
        t.configure(bg="#f4f6f9"); t.transient(self.winfo_toplevel())
        t.after(150, t.grab_set)
        tk.Label(t, text="Couleur de chaque salle / atelier", bg="#0056b3", fg="white",
                 font=("Segoe UI", 12, "bold"), anchor="w", padx=12, pady=8).pack(fill="x")
        tk.Label(t, text="Cliquez sur une couleur pour l'appliquer à la salle. "
                         "« Auto » revient à la couleur automatique.",
                 bg="#f4f6f9", fg="#555", wraplength=560, justify="left",
                 font=("Segoe UI", 10)).pack(anchor="w", padx=12, pady=6)
        body = tk.Frame(t, bg="#f4f6f9"); body.pack(fill="both", expand=True, padx=10, pady=6)

        if not D["espaces"]:
            tk.Label(body, text="Aucune salle ni atelier. Ajoutez-les dans Paramètres > Espace.",
                     bg="#f4f6f9", fg="#555").pack(pady=16)

        def applique(eid, col):
            D.setdefault("couleurs", {})
            if col is None:
                D["couleurs"].pop(str(eid), None)
            else:
                D["couleurs"][str(eid)] = col
            self.autosave()
            self.refresh()
            maj()

        def maj():
            for w in body.winfo_children():
                w.destroy()
            for n, e in enumerate(D["espaces"]):
                lig = tk.Frame(body, bg="#ffffff", bd=1, relief="solid")
                lig.pack(fill="x", pady=3, padx=2)
                act = tt_color(D, e["id"])
                tk.Label(lig, text=f"{e['nom']}  ({e['type']})", width=22, anchor="w",
                         bg="#ffffff", font=("Segoe UI", 10, "bold")).pack(side="left", padx=8, pady=6)
                for col in CHOIX:
                    b = tk.Button(lig, bg=col, activebackground=col, width=2, bd=0,
                                  relief="solid" if col == act else "flat",
                                  highlightthickness=2 if col == act else 0,
                                  highlightcolor="#000000",
                                  cursor="hand2",
                                  command=lambda i=e["id"], c=col: applique(i, c))
                    b.pack(side="left", padx=2, pady=6)
                tk.Button(lig, text="Auto", font=("Segoe UI", 9), bg="#e9ecef",
                          activebackground="#d5dce5", bd=0, padx=8, cursor="hand2",
                          command=lambda i=e["id"]: applique(i, None)).pack(side="left", padx=8, pady=6)
        maj()
        tk.Button(t, text="Fermer", font=("Segoe UI", 10, "bold"), bg="#0056b3", fg="white",
                  activebackground="#003d82", activeforeground="white", bd=0, padx=20, pady=6,
                  cursor="hand2", command=t.destroy).pack(pady=10)

    # ---------- formateurs = Personnel (permanents) + Vacataires ----------
    def sync_formateurs(self, reset=False):
        """Ajoute a la liste des formateurs ceux du module Personnel (permanents) et du module
        Vacataires. Ne touche pas aux fiches Personnel / Vacataires ; les formateurs retires ici
        ne reviennent pas (sauf bouton « Recharger »)."""
        D = self.D
        if reset: D["fmt_ignores"] = []
        ign = set(D.get("fmt_ignores", []))
        try:
            with get_db_connection() as conn:
                pers = conn.execute("SELECT id, nom, prenom, cin, fonction FROM personnel").fetchall()
                vacs = conn.execute("SELECT id, nom, prenom, cin FROM vacataires").fetchall()
        except Exception:
            return
        pf = [r for r in pers if re.search(r"formate|formatri", tt_norm(r[4]))]
        if not pf: pf = list(pers)            # fonction non renseignee : on prend tout le personnel
        items = [(f"p:{r[0]}", r[1], r[2], r[3], "Permanent") for r in pf] + \
                [(f"v:{r[0]}", r[1], r[2], r[3], "Vacataire") for r in vacs]
        changed = False
        for src, nom, prenom, cin, typ in items:
            if src in ign: continue
            nom, prenom = (nom or "").strip(), (prenom or "").strip()
            if not (nom or prenom): continue
            toks = sorted(tt_norm(f"{nom} {prenom}").split())
            if not prenom: nom, prenom = tt_split_name(nom)      # "NOM PRENOM" saisi dans un seul champ
            x = next((f for f in D["formateurs"] if f.get("src") == src), None) or \
                next((f for f in D["formateurs"] if not f.get("src") and sorted(tt_norm(tt_fname(f)).split()) == toks), None)
            if x:
                if not x.get("src"):
                    x["src"] = src; x["type"] = typ; x["nom"], x["prenom"] = nom, prenom
                    if not x.get("matricule"): x["matricule"] = cin or ""
                    changed = True
                continue
            D["formateurs"].append({"id": self.uid(), "nom": nom, "prenom": prenom, "matricule": cin or "", "type": typ, "src": src})
            changed = True
        for f in D["formateurs"]:               # fiches deja creees avec le nom complet dans "Nom"
            if not (f.get("prenom") or "").strip() and len((f.get("nom") or "").split()) > 1:
                f["nom"], f["prenom"] = tt_split_name(f["nom"]); changed = True
        if changed:
            D["formateurs"].sort(key=lambda f: (f.get("type") != "Permanent", tt_norm(tt_fname(f))))
            self.autosave()

    # ---------- import eNote ----------
    def import_enote(self):
        if self.mode != "enote":
            if messagebox.askyesno("Importer séances eNote",
                                   "L'import eNote alimente l'« Emploi eNote ».\nL'emploi établi par le directeur reste intact.\n\n"
                                   "Basculer vers l'Emploi eNote maintenant ?"):
                self.switch_mode("enote")
            return
        top = self.winfo_toplevel()
        self.sync_formateurs()
        paths = filedialog.askopenfilenames(parent=top, title="Fichiers Excel exportés depuis eNote (Export Excel)",
                                            filetypes=[("Excel / CSV", "*.xlsx *.xls *.csv"), ("Tous les fichiers", "*.*")])
        if not paths: return
        lots, erreurs = [], []
        for p in paths:
            try: rows = tt_enote_load(p)
            except Exception as ex: erreurs.append(f"{os.path.basename(p)} : {ex}"); continue
            if rows: lots.append((p, rows))
            else: erreurs.append(f"{os.path.basename(p)} : aucune séance trouvée")
        if not lots:
            return messagebox.showerror("Import eNote", "Aucun fichier exploitable.\n\n" + "\n".join(erreurs))

        # semaines presentes dans les fichiers
        cnt, lab = {}, {}
        for _, rows in lots:
            for r in rows:
                lu = r["date"] - timedelta(days=r["date"].weekday())
                cnt[lu] = cnt.get(lu, 0) + 1
                m = re.match(r"\s*(S\d+)", r["semaine"] or "")
                if m and lu not in lab: lab[lu] = m.group(1)
        semaines = sorted(cnt, reverse=True)
        sem_txt = [f"{(lab[l] + '  ') if l in lab else ''}du {l.strftime('%d/%m/%Y')} au {(l + timedelta(days=5)).strftime('%d/%m/%Y')}  ({cnt[l]} séances)"
                   for l in semaines]
        best = max(range(len(semaines)), key=lambda i: (cnt[semaines[i]], -i))

        noms = [tt_fname(x) for x in self.D["formateurs"]]
        memo_path = os.path.join(os.path.dirname(ENOTE_EMPLOI_FILE), "enote_formateurs.json")   # fichier -> formateur (memoire)
        try:
            with open(memo_path, encoding="utf-8") as fh: memo = json.load(fh)
        except Exception:
            memo = {}
        STOP = {"xlsx", "xls", "csv", "etat", "etatxls", "emploi", "enote", "edt", "export", "copie", "copy"}
        def fkey(path):
            return " ".join(t for t in tt_norm(os.path.splitext(os.path.basename(path))[0].replace("_", " ").replace("-", " ").replace(".", " ")).split()
                            if t not in STOP and not t.isdigit())
        def sim(a, b):
            if a == b: return 1.0
            if len(a) >= 3 and len(b) >= 3 and (a.startswith(b) or b.startswith(a)): return 0.9       # atman ~ atmane
            return difflib.SequenceMatcher(None, a, b).ratio()
        def devine(path, rows):
            det = next((r["formateur"] for r in rows if r["formateur"]), "")
            if det: return det
            key = fkey(path)
            if memo.get(key) in noms: return memo[key]                      # deja choisi une fois : on s'en souvient
            toks = key.split()
            if not toks: return ""
            scores = []
            for x in self.D["formateurs"]:
                nt = tt_norm(tt_fname(x)).split()
                if not nt: continue
                sc = sum(max(sim(t, u) for u in nt) for t in toks) / len(toks)       # chaque mot du fichier ~ un mot du nom
                sc = max(sc, sim("".join(toks), "".join(nt)))                       # el khadiri ~ elkhadiri
                scores.append((sc, tt_fname(x)))
            scores.sort(reverse=True)
            if scores and scores[0][0] >= 0.85 and (len(scores) == 1 or scores[0][0] - scores[1][0] >= 0.1):
                return scores[0][1]
            return ""                                                       # introuvable ou ambigu : a choisir a la main

        t = tk.Toplevel(self); t.title("Importer les séances eNote"); t.transient(top); t.after(150, t.grab_set)
        ttk.Label(t, text="Semaine à importer :").grid(row=0, column=0, sticky="w", padx=10, pady=(10, 4))
        cs = ttk.Combobox(t, values=sem_txt, state="readonly", width=52); cs.grid(row=0, column=1, padx=10, pady=(10, 4)); cs.current(best)
        ttk.Label(t, text="Formateur de chaque fichier :").grid(row=1, column=0, columnspan=2, sticky="w", padx=10, pady=(8, 2))
        cfs = []
        for i, (p, rows) in enumerate(lots):
            ttk.Label(t, text=f"{os.path.basename(p)}  ({len(rows)} séances)").grid(row=2 + i, column=0, sticky="w", padx=10, pady=2)
            c = ttk.Combobox(t, values=noms, width=52); c.grid(row=2 + i, column=1, padx=10, pady=2); c.set(devine(p, rows)); cfs.append(c)
        r0 = 2 + len(lots)
        info = "Les salles ne figurent pas dans eNote : le logiciel choisit une salle libre (vos salles d'abord)."
        if erreurs: info += "\n\nFichiers ignorés :\n" + "\n".join(erreurs)
        ttk.Label(t, text=info, foreground="#555", wraplength=520, justify="left").grid(row=r0, column=0, columnspan=2, sticky="w", padx=10, pady=8)

        def ok():
            fnoms = [c.get().strip() for c in cfs]
            for (p, rows), fn in zip(lots, fnoms):
                if not fn and not all(r["formateur"] for r in rows):
                    return messagebox.showwarning("Import eNote", f"Indiquez le formateur du fichier :\n{os.path.basename(p)}", parent=t)
            for (p, rows), fn in zip(lots, fnoms):                      # memorise fichier -> formateur pour les prochains imports
                if fn and fkey(p): memo[fkey(p)] = fn
            try: atomic_write_json(memo_path, memo, indent=1)
            except Exception: logger.exception("Memoire des formateurs eNote non enregistree")
            rep = tt_enote_apply(self.D, self.uid, [(fn, rows) for (p, rows), fn in zip(lots, fnoms)], semaines[cs.current()])
            t.destroy(); self.refresh()
            msg = f"{rep['ajoutees']} séance(s) ajoutée(s)."
            if rep["par_formateur"]: msg += "\n" + "\n".join(f"- {k} : {v}" for k, v in rep["par_formateur"].items())
            if rep["deja"]: msg += f"\n{rep['deja']} déjà présente(s) (ignorée(s))."
            if rep["crees"]: msg += "\n\nCréé automatiquement :\n- " + "\n- ".join(rep["crees"][:12]) + ("\n..." if len(rep["crees"]) > 12 else "")
            if rep["conflits"]: msg += "\n\nNon placées (conflit) :\n- " + "\n- ".join(rep["conflits"][:10]) + ("\n..." if len(rep["conflits"]) > 10 else "")
            if rep["ignorees"]: msg += "\n\nIgnorées :\n- " + "\n- ".join(rep["ignorees"][:10])
            messagebox.showinfo("Import eNote", msg)
        b = ttk.Frame(t); b.grid(row=r0 + 1, column=0, columnspan=2, pady=10)
        ttk.Button(b, text="Importer", command=ok).pack(side="left", padx=4)
        ttk.Button(b, text="Annuler", command=t.destroy).pack(side="left", padx=4)


# ------------------------------------------------------------------
# CHARTE GRAPHIQUE : palette et style ttk moderne (tout le logiciel)
# ------------------------------------------------------------------
PALETTE = {
    "primary": "#0056b3", "primary_dark": "#003d82", "accent": "#e8a020",
    "success": "#1b8a5a", "danger": "#c0392b", "purple": "#6a4fb3",
    "teal": "#0e7c66", "navy": "#0a2a52", "text": "#33475b", "muted": "#6b7a89",
}

def setup_modern_ttk_style(root):
    """Style 'clam' personnalise : tableaux, onglets, boutons, listes...
    Donne aux widgets ttk (module Emploi du temps, analyses...) une
    presentation moderne et coherente avec le reste de l'application."""
    st = ttk.Style(root)
    try:
        st.theme_use("clam")
    except tk.TclError:
        pass
    f = "Segoe UI"
    st.configure(".", font=(f, 10))
    st.configure("Treeview", font=(f, 10), rowheight=28, fieldbackground="#ffffff",
                 background="#ffffff", borderwidth=0)
    st.configure("Treeview.Heading", font=(f, 10, "bold"), padding=(8, 8),
                 background=PALETTE["primary"], foreground="#ffffff", relief="flat", borderwidth=0)
    st.map("Treeview.Heading", background=[("active", PALETTE["primary_dark"])])
    st.map("Treeview", background=[("selected", "#dbe7f5")],
           foreground=[("selected", PALETTE["navy"])])
    st.configure("TNotebook", background="#eef1f5", borderwidth=0, tabmargins=(6, 4, 6, 0))
    st.configure("TNotebook.Tab", font=(f, 10, "bold"), padding=(16, 8),
                 background="#d7dee8", foreground=PALETTE["text"])
    st.map("TNotebook.Tab", background=[("selected", "#ffffff")],
           foreground=[("selected", PALETTE["primary"])])
    st.configure("TButton", font=(f, 10, "bold"), padding=(16, 9), borderwidth=0, focusthickness=0,
                 cursor="hand2", background=PALETTE["primary"], foreground="#ffffff")
    st.map("TButton", background=[("active", PALETTE["primary_dark"]),
                                  ("pressed", PALETTE["primary_dark"])])
    # Boutons d'action de la barre d'outils : MEME forme partout, couleur = fonction
    for nom, col, hov in (("ToolBlue", "#0056b3", "#003d82"),
                          ("ToolGrey", "#8e99a4", "#6f7a85"),
                          ("ToolGreen", "#068a4e", "#057a44"),
                          ("ToolOrange", "#d98219", "#a96112")):
        st.configure(f"{nom}.TButton", font=(f, 10, "bold"), padding=(16, 9),
                     borderwidth=0, focusthickness=0, cursor="hand2",
                     background=col, foreground="#ffffff")
        st.map(f"{nom}.TButton", background=[("active", hov), ("pressed", hov)])
    st.configure("TCombobox", font=(f, 10), padding=5, fieldbackground="#ffffff")
    st.configure("TEntry", font=(f, 10), padding=5, fieldbackground="#ffffff")
    st.configure("TFrame", background="#f4f6f9")
    st.configure("TLabelframe", background="#f4f6f9", bordercolor="#d5dce5")
    st.configure("TLabelframe.Label", background="#f4f6f9",
                 foreground=PALETTE["primary"], font=(f, 10, "bold"))
    st.configure("TRadiobutton", background="#f4f6f9", foreground=PALETTE["text"])
    st.configure("TCheckbutton", background="#ffffff", foreground=PALETTE["text"])
    st.configure("TLabel", background="#f4f6f9", foreground=PALETTE["text"])
    st.configure("Vertical.TScrollbar", background="#c9d4e0", troughcolor="#eef1f5",
                 borderwidth=0, arrowcolor=PALETTE["text"], width=12)
    st.configure("Horizontal.TScrollbar", background="#c9d4e0", troughcolor="#eef1f5",
                 borderwidth=0, arrowcolor=PALETTE["text"], width=12)


class Application(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("OFPPT - GESTION ADMINISTRATIVE (CF BERKANE)")
        self.geometry("1200x720")
        setup_modern_ttk_style(self)

        self.init_db()

        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)

        self._nav = {}
        self.sidebar = ctk.CTkFrame(self, width=236, corner_radius=0, fg_color=PALETTE["navy"])
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.grid_propagate(False)

        # ---------- entete sidebar : logo + titres ----------
        _head = ctk.CTkFrame(self.sidebar, fg_color="transparent")
        _head.pack(fill="x", padx=14, pady=(18, 6))
        self._side_logo = None
        try:
            from PIL import Image
            _src = next((p for p in (os.path.join(BASE_DIR, "logo_ofppt.png"),
                                     os.path.join(BASE_DIR, "logo_ofppt.jpg")) if os.path.exists(p)), None)
            if _src:
                _img = Image.open(_src).convert("RGBA")
                _w, _h = _img.size
                self._side_logo = ctk.CTkImage(light_image=_img, dark_image=_img,
                                               size=(max(1, int(_w * 40 / _h)), 40))
        except Exception:
            self._side_logo = None
        if self._side_logo:
            ctk.CTkLabel(_head, image=self._side_logo, text="").pack(side="left")
        else:
            ctk.CTkLabel(_head, text="OFPPT", font=ctk.CTkFont(size=20, weight="bold"),
                         text_color=PALETTE["accent"]).pack(side="left")
        _ttl = ctk.CTkFrame(_head, fg_color="transparent")
        _ttl.pack(side="left", padx=10)
        ctk.CTkLabel(_ttl, text="GESTION ADMIN", font=ctk.CTkFont(size=14, weight="bold"),
                     text_color="white").pack(anchor="w")
        ctk.CTkLabel(_ttl, text="CF BERKANE", font=ctk.CTkFont(size=11),
                     text_color="#9db8d9").pack(anchor="w")
        ctk.CTkFrame(self.sidebar, height=2, fg_color=PALETTE["accent"]).pack(fill="x", padx=14, pady=(2, 10))

        # --- BOUTONS MENU LATERAL ---
        btn_accueil = self._nav_btn("Accueil", self.show_accueil, "accueil")
        btn_accueil.pack(fill="x", padx=14, pady=3)

        btn_personnel = self._nav_btn("Personnel", self.show_personnel, "personnel")
        btn_personnel.pack(fill="x", padx=14, pady=3)

        btn_formateurs = self._nav_btn("Formateurs", self.show_formateurs, "formateurs")
        btn_formateurs.pack(fill="x", padx=14, pady=3)

        btn_analysis = self._nav_btn("Analyse", self.show_analysis, "analyse")
        btn_analysis.pack(fill="x", padx=14, pady=3)

        # Bouton Tableau de service (import Excel DRIF + affectation des modules)
        btn_ts = self._nav_btn("Tableau de service", self.show_tableau_service, "ts")
        btn_ts.pack(fill="x", padx=14, pady=3)

        btn_vacataires = self._nav_btn("Vacataires", self.show_vacataires, "vacataires")
        btn_vacataires.pack(fill="x", padx=14, pady=3)

        btn_absence_menu = self._nav_btn("Suivi d'absence", self.show_suivi_absence, "absences")
        btn_absence_menu.pack(fill="x", padx=14, pady=3)

        btn_formation_menu = self._nav_btn("Formation", self.show_formation, "formation")
        btn_formation_menu.pack(fill="x", padx=14, pady=3)

        # Bouton Ordre de mission
        btn_ordre_mission = self._nav_btn("Ordre de mission", self.show_ordre_mission_module, "om")
        btn_ordre_mission.pack(fill="x", padx=14, pady=3)

        # NOUVEAU BOUTON : Emploi (Espaces, Groupes et Emploi du temps)
        btn_emploi = self._nav_btn("Emploi du temps", lambda: self.show_emploi_module("directeur"), "emploi")
        btn_emploi.pack(fill="x", padx=14, pady=3)

        # Emploi du temps établi d'après eNote (second emploi, fichier séparé)
        btn_emploi_enote = self._nav_btn("Emploi eNote", lambda: self.show_emploi_module("enote"), "emploi_enote")
        btn_emploi_enote.pack(fill="x", padx=14, pady=3)

        # Bouton Paramètres ouvrant la fenêtre des paramètres avec la gestion des comptes
        btn_settings = self._nav_btn("Paramètres", lambda: SettingsWindow(self, self.logout), "settings")
        btn_settings.pack(side="bottom", fill="x", padx=14, pady=(3, 8))
        ctk.CTkLabel(self.sidebar, text="v2.0  ·  © 2026 OFPPT", font=ctk.CTkFont(size=10),
                     text_color="#5d7ba3").pack(side="bottom", pady=(0, 6))

        self.main_frame = ctk.CTkFrame(self)
        self.main_frame.grid(row=0, column=1, sticky="nsew", padx=20, pady=20)

        self.show_accueil()
        # Vérifie périodiquement l'analyse automatique du lundi à 10 h.
        self.after(1000, self.check_scheduled_analysis)

    # ---------- navigation laterale (etat actif surligne) ----------
    def _nav_btn(self, text, command, key):
        b = ctk.CTkButton(self.sidebar, text="      " + text,
                          font=ctk.CTkFont(size=13, weight="bold"),
                          height=42, corner_radius=11, anchor="w",
                          fg_color="transparent", hover_color="#123a6b",
                          text_color="#c8d6ea", border_width=0,
                          command=lambda: (self.set_active_nav(key), command()))
        self._nav[key] = b
        return b

    def set_active_nav(self, key):
        for k, b in getattr(self, "_nav", {}).items():
            actif = (k == key)
            b.configure(fg_color=("#0056b3" if actif else "transparent"),
                        text_color=("white" if actif else "#c8d6ea"),
                        border_width=0)

    def logout(self):
        self.destroy()
        if not REQUIRE_LOGIN:          # pas de mot de passe : "Deconnexion" ferme simplement le logiciel
            return
        login_app = LoginWindow(on_login_success=launch_main_app)
        login_app.mainloop()

    def init_db(self):
        with get_db_connection() as conn:
            cursor = conn.cursor()

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS personnel (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    nom TEXT NOT NULL,
                    prenom TEXT NOT NULL,
                    cin TEXT UNIQUE,
                    specialite TEXT,
                    type_f TEXT,
                    fonction TEXT,
                    echelle TEXT,
                    categorie TEXT
                )
            ''')

            # Colonne salaire de base (pour l'attestation de salaire)
            cursor.execute("PRAGMA table_info(personnel)")
            pers_cols = [c[1] for c in cursor.fetchall()]
            if "salaire" not in pers_cols:
                cursor.execute("ALTER TABLE personnel ADD COLUMN salaire TEXT")
            # Masse horaire statutaire hebdomadaire (h/semaine) : sert a calculer les heures supp (page Analyse)
            if "masse_statutaire" not in pers_cols:
                cursor.execute("ALTER TABLE personnel ADD COLUMN masse_statutaire REAL")

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS ordres_mission (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    nom TEXT,
                    motif TEXT,
                    destination TEXT,
                    transport TEXT,
                    date_mission TEXT
                )
            ''')

            # Colonnes supplementaires : lien avec le personnel / la formation + dates complètes
            cursor.execute("PRAGMA table_info(ordres_mission)")
            om_cols = [c[1] for c in cursor.fetchall()]
            for col, typ in [("personnel_id", "INTEGER"), ("formation_id", "INTEGER"), ("date_retour", "TEXT"),
                             ("heure_dep", "TEXT"), ("heure_ret", "TEXT"), ("num", "TEXT")]:
                if col not in om_cols:
                    cursor.execute(f"ALTER TABLE ordres_mission ADD COLUMN {col} {typ}")

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS vacataires (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    nom TEXT NOT NULL,
                    prenom TEXT NOT NULL,
                    cin TEXT,
                    telephone TEXT,
                    specialite TEXT,
                    filiere TEXT,
                    heures REAL DEFAULT 0,
                    taux REAL DEFAULT 0
                )
            ''')

            # Colonnes du module vacataires : CIN, Nom et Prénom, MHA, Statut, Affectation
            cursor.execute("PRAGMA table_info(vacataires)")
            vac_cols = [c[1] for c in cursor.fetchall()]
            for col in ("mha", "statut", "affectation"):
                if col not in vac_cols:
                    cursor.execute(f"ALTER TABLE vacataires ADD COLUMN {col} TEXT")

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS absences (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    personnel_id INTEGER,
                    motif TEXT NOT NULL,
                    date_debut TEXT NOT NULL,
                    date_fin TEXT NOT NULL,
                    FOREIGN KEY (personnel_id) REFERENCES personnel (id) ON DELETE CASCADE
                )
            ''')

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS formations (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    personnel_id INTEGER,
                    theme TEXT NOT NULL,
                    lieu TEXT NOT NULL,
                    date_debut TEXT NOT NULL,
                    date_fin TEXT NOT NULL,
                    FOREIGN KEY (personnel_id) REFERENCES personnel (id) ON DELETE CASCADE
                )
            ''')

            # NOUVELLES TABLES POUR LES ESPACES, GROUPES ET EMPLOIS DU TEMPS
            cursor.execute('''
                CREATE TABLE IF NOT EXISTS espaces (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    nom TEXT UNIQUE NOT NULL,
                    type TEXT
                )
            ''')

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS groupes (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    nom TEXT UNIQUE NOT NULL,
                    filiere TEXT
                )
            ''')

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS emplois (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    groupe_id INTEGER,
                    espace_id INTEGER,
                    jour TEXT,
                    horaire TEXT,
                    matiere TEXT,
                    FOREIGN KEY (groupe_id) REFERENCES groupes (id) ON DELETE CASCADE,
                    FOREIGN KEY (espace_id) REFERENCES espaces (id) ON DELETE SET NULL
                )
            ''')

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS users (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    username TEXT UNIQUE,
                    password TEXT,
                    role TEXT
                )
            ''')

            # TABLEAU DE SERVICE : import Excel DRIF + affectation des modules aux formateurs
            # BULLETIN DE PAIE (scan + lignes de paie) -> attestation de salaire
            cursor.execute(bulletin_create_sql())

            cursor.execute("PRAGMA table_info(bulletin_paie)")
            bp_cols = [c[1] for c in cursor.fetchall()]
            if "alloc_familiales" not in bp_cols:
                cursor.execute("ALTER TABLE bulletin_paie ADD COLUMN alloc_familiales TEXT")
            if "hrs_supp" not in bp_cols:
                cursor.execute("ALTER TABLE bulletin_paie ADD COLUMN hrs_supp TEXT")
            migrate_bulletin_money(conn)          # montants stockes en nombres (schema v1)

            cursor.execute('''
                CREATE TABLE IF NOT EXISTS tableau_service (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    exercice TEXT, code_secteur_groupe TEXT, secteur_groupe TEXT, code_secteur TEXT,
                    secteur TEXT, niveau TEXT, type_formation TEXT, creneau TEXT,
                    code_filiere_drif TEXT, intitule_filiere_drif TEXT, code_tc_carte TEXT,
                    code_filiere_carte TEXT, filiere TEXT, filiere_ar TEXT, annee_formation TEXT,
                    code_module TEXT, module TEXT, module_ar TEXT,
                    mhp_s1 TEXT, mhsyn_s1 TEXT, mhasyn_s1 TEXT, mhd_s1 TEXT, mht_s1 TEXT,
                    mhp_s2 TEXT, mhsyn_s2 TEXT, mhasyn_s2 TEXT, mhd_s2 TEXT, mht_s2 TEXT,
                    mhp_totale TEXT, mhd_totale TEXT, mh_stage TEXT, mht TEXT,
                    coef TEXT, efm_regional TEXT, operation TEXT,
                    groupe TEXT, mle TEXT, formateur TEXT, affectation TEXT
                )
            ''')

            conn.commit()

    def clear_main_frame(self):
        for widget in self.main_frame.winfo_children():
            widget.destroy()

    def open_pdf_viewer(self, pdf_instance, default_filename, doc_title):
        try:
            temp_file_path = temp_pdf_path(default_filename)
            pdf_instance.output(temp_file_path)

            if sys.platform == "win32":
                os.startfile(temp_file_path)
            elif sys.platform == "darwin":
                subprocess.run(["open", temp_file_path])
            else:
                subprocess.run(["xdg-open", temp_file_path])

            if messagebox.askyesno("Aperçu généré", f"{doc_title} est ouvert à l'écran.\n\nSouhaitez-vous en enregistrer une copie sur votre ordinateur ?"):
                path = filedialog.asksaveasfilename(
                    defaultextension=".pdf",
                    filetypes=[("PDF files", "*.pdf")],
                    initialfile=default_filename
                )
                if path:
                    shutil.copy(temp_file_path, path)
                    messagebox.showinfo("Succès", "Fichier enregistré avec succès !")
        except Exception as e:
            messagebox.showerror("Erreur PDF", f"Impossible d'ouvrir ou d'enregistrer le PDF : {str(e)}")

    # --- MODULE EMPLOI (TIME TABLE : emplois du temps, groupes, formateurs, espaces) ---
    def show_emploi_module(self, mode=None):
        mode = mode if mode in ("directeur", "enote") else getattr(self, "_tt_mode", "directeur")
        self._tt_mode = mode
        self.set_active_nav("emploi" if mode == "directeur" else "emploi_enote")     # surligne le bon bouton du menu latéral
        self.clear_main_frame()
        TimeTableFrame(self.main_frame, on_quit=self.show_accueil, mode=mode,
                       on_switch=self.show_emploi_module).pack(fill="both", expand=True)

    # --- MODULE ORDRE DE MISSION (ACCES DEPUIS LE MENU) ---
    def show_ordre_mission_module(self):
        self.clear_main_frame()

        top_frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        top_frame.pack(fill="x", padx=20, pady=10)

        title = ctk.CTkLabel(top_frame, text="Gestion des Ordres de Mission", font=ctk.CTkFont(size=20, weight="bold"))
        title.pack(side="left")

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT id, nom, prenom, cin, specialite, fonction, echelle, categorie FROM personnel ORDER BY nom ASC")
            personnel_rows = cursor.fetchall()
            
            cursor.execute("SELECT id, nom, motif, destination, transport, date_mission, personnel_id, date_retour, heure_dep, heure_ret, num, formation_id FROM ordres_mission ORDER BY id DESC")
            om_rows = cursor.fetchall()

        if not personnel_rows:
            ctk.CTkLabel(self.main_frame, text="Aucun agent enregistré. Veuillez ajouter du personnel d'abord.", font=ctk.CTkFont(size=14)).pack(pady=40)
            return

        gen_frame = ctk.CTkFrame(self.main_frame, corner_radius=10)
        gen_frame.pack(fill="x", padx=20, pady=10)

        lbl_gen_title = ctk.CTkLabel(gen_frame, text="Créer un nouvel Ordre de Mission", font=ctk.CTkFont(size=14, weight="bold"))
        lbl_gen_title.pack(anchor="w", padx=15, pady=(10, 5))

        select_p_frame = ctk.CTkFrame(gen_frame, fg_color="transparent")
        select_p_frame.pack(fill="x", padx=15, pady=5)

        ctk.CTkLabel(select_p_frame, text="Sélectionner l'agent :", width=140, anchor="w", font=ctk.CTkFont(weight="bold")).pack(side="left")
        
        personnel_map = {f"{p[1].upper()} {p[2]} (CIN: {p[3]})": p for p in personnel_rows}
        combo_personnel = ctk.CTkOptionMenu(select_p_frame, values=list(personnel_map.keys()), fg_color=MAIN_COLOR, button_color=MAIN_COLOR_HOVER)
        combo_personnel.pack(side="left", fill="x", expand=True)

        btn_open_om = ctk.CTkButton(gen_frame, text="Renseigner les détails de la mission...", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=lambda: self.trigger_om_dialog(personnel_map, combo_personnel.get()))
        btn_open_om.pack(pady=12)

        lbl_hist_title = ctk.CTkLabel(self.main_frame, text="Historique des Ordres de Mission enregistrés", font=ctk.CTkFont(size=14, weight="bold"))
        lbl_hist_title.pack(anchor="w", padx=20, pady=(15, 5))

        scroll_om = ctk.CTkScrollableFrame(self.main_frame)
        scroll_om.pack(fill="both", expand=True, padx=20, pady=(0, 15))

        if not om_rows:
            ctk.CTkLabel(scroll_om, text="Aucun ordre de mission enregistré pour le moment.", font=ctk.CTkFont(slant="italic")).pack(pady=20)
            return

        for om in om_rows:
            om_id, nom_ag, motif_m, dest_m, transp_m, date_m, p_id_m, date_r, h_dep, h_ret, num_m, form_id = om
            card = ctk.CTkFrame(scroll_om)
            card.pack(fill="x", pady=4, padx=5)

            periode = f"Du {date_m} ({h_dep or '--:--'}) au {date_r} ({h_ret or '--:--'})" if date_r else f"Le {date_m}"
            origine = "  [Formation]" if form_id else ""
            info = f"Agent : {nom_ag} | Destination : {dest_m} | Motif : {motif_m} | {periode} | Transport : {transp_m}{origine}"
            lbl = ctk.CTkLabel(card, text=info, font=ctk.CTkFont(size=12, weight="bold"), wraplength=560, justify="left")
            lbl.pack(side="left", padx=10, pady=8)

            btn_del_om = ctk.CTkButton(card, text="Supprimer", fg_color="#a83232", hover_color="#7e2424", width=70, height=24, command=lambda id_=om_id: self.delete_ordre_mission(id_))
            btn_del_om.pack(side="right", padx=(4, 10), pady=8)

            if p_id_m:
                btn_pdf_om = ctk.CTkButton(card, text="Ouvrir / PDF", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, width=90, height=24, command=lambda o=om: self.open_saved_om(o))
                btn_pdf_om.pack(side="right", padx=4, pady=8)

    def open_saved_om(self, om):
        """Rouvre un ordre de mission enregistre (ex: cree depuis une formation) avec toutes ses informations."""
        om_id, nom_ag, motif_m, dest_m, transp_m, date_m, p_id_m, date_r, h_dep, h_ret, num_m, form_id = om
        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT id, nom, prenom, cin, specialite, fonction, echelle, categorie FROM personnel WHERE id=?", (p_id_m,))
            personnel_data = cursor.fetchone()
        if not personnel_data:
            messagebox.showerror("Erreur", "L'agent de cet ordre de mission n'existe plus.")
            return
        initial = {
            "om_id": om_id, "num": num_m or "", "destination": dest_m, "motif": motif_m,
            "date_dep": date_m, "heure_dep": h_dep or "08:00",
            "date_ret": date_r or date_m, "heure_ret": h_ret or "18:00",
            "transport_type": transp_m or "Public",
        }
        OrdreMissionDialog(self, personnel_data, self.generate_om_pdf, initial_data=initial)

    def trigger_om_dialog(self, personnel_map, selected_key):
        if not selected_key or selected_key not in personnel_map:
            messagebox.showerror("Erreur", "Veuillez sélectionner un agent valide.")
            return
        personnel_data = personnel_map[selected_key]
        OrdreMissionDialog(self, personnel_data, self.generate_om_pdf)

    def delete_ordre_mission(self, om_id):
        if messagebox.askyesno("Confirmation", "Voulez-vous supprimer cet ordre de mission de l'historique ?"):
            with get_db_connection() as conn:
                cursor = conn.cursor()
                cursor.execute("DELETE FROM ordres_mission WHERE id=?", (om_id,))
                conn.commit()
            self.show_ordre_mission_module()

    # --- PAGE ANALYSE ---
    def show_analysis(self):
        """Page dédiée à l'analyse manuelle et automatique des séances."""
        self.clear_main_frame()
        frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        frame.pack(fill="both", expand=True, padx=25, pady=25)

        ctk.CTkLabel(frame, text="Analyse des emplois du temps", font=ctk.CTkFont(size=24, weight="bold")).pack(anchor="w")
        ctk.CTkLabel(
            frame,
            text="Cette page affiche la masse horaire des formateurs, calculée d'après l'emploi du temps, quand vous le souhaitez et d'activer son lancement automatique chaque lundi à 10:00.",
            font=ctk.CTkFont(size=13), justify="left", wraplength=850
        ).pack(anchor="w", pady=(5, 20))

        box = ctk.CTkFrame(frame, corner_radius=12, border_width=1, border_color="#d5dce5")
        box.pack(fill="x", pady=8)
        ctk.CTkLabel(box, text="Mode manuel", font=ctk.CTkFont(size=17, weight="bold")).pack(anchor="w", padx=20, pady=(18, 4))
        ctk.CTkLabel(box, text="Cliquez sur le bouton pour afficher immédiatement le tableau de la masse horaire de chaque formateur (par jour et par semaine).", justify="left").pack(anchor="w", padx=20, pady=4)
        ctk.CTkButton(box, text="Lancer l'analyse maintenant", width=220, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.run_analysis_now).pack(anchor="w", padx=20, pady=(8, 8))
        ctk.CTkLabel(box, text="Ou importez un ou plusieurs fichiers Excel (eNote) : l'analyse est calculée semaine par semaine.", justify="left").pack(anchor="w", padx=20, pady=(6, 4))
        ctk.CTkButton(box, text="Importer des fichiers Excel", width=220, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.import_analysis_files).pack(anchor="w", padx=20, pady=(4, 18))

        auto = ctk.CTkFrame(frame, corner_radius=12, border_width=1, border_color="#d5dce5")
        auto.pack(fill="x", pady=8)
        ctk.CTkLabel(auto, text="Mode automatique", font=ctk.CTkFont(size=17, weight="bold")).pack(anchor="w", padx=20, pady=(18, 4))
        ctk.CTkLabel(auto, text="L'application doit être ouverte. Le lundi à 10:00, l'analyse sera lancée une seule fois.", justify="left").pack(anchor="w", padx=20, pady=4)
        settings = self._analysis_settings()
        self.auto_analysis_var = tk.BooleanVar(value=bool(settings.get("enabled")))
        ctk.CTkCheckBox(auto, text="Activer l'analyse automatique chaque lundi à 10:00", variable=self.auto_analysis_var, command=self.set_auto_analysis).pack(anchor="w", padx=20, pady=(10, 4))
        self.analysis_status_label = ctk.CTkLabel(auto, text="", font=ctk.CTkFont(size=12))
        self.analysis_status_label.pack(anchor="w", padx=20, pady=(0, 18))
        self.set_auto_analysis()

    # --- HEURES SUPPLEMENTAIRES : masse statutaire (fiche formateur) vs heures travaillees (emploi du temps) ---
    def _stat_map(self):
        """{cle du nom : masse statutaire hebdomadaire (h)} pour les formateurs qui en ont une."""
        out = {}
        with get_db_connection() as conn:
            for n, p, m in conn.execute("SELECT nom, prenom, masse_statutaire FROM personnel"):
                try:
                    v = float(str(m).replace(",", "."))
                except (TypeError, ValueError):
                    v = 0.0
                if v > 0:
                    out[self._name_key(f"{n} {p}")] = v
        return out

    def _hs_week(self, smap, nom, q):
        """(masse statutaire, heures supp) pour q quarts d'heure travailles dans la semaine.
        Heures supp = heures travaillees - masse statutaire (jamais negatif). (None, 0) si masse non renseignee."""
        st = smap.get(self._name_key(nom))
        if not st:
            return None, 0.0
        return st, max(0.0, q / 4.0 - st)

    def _append_hs_sheet(self, path, res, smap):
        """Ajoute une feuille « Heures supp » au fichier Excel d'analyse deja enregistre."""
        try:
            import openpyxl
            from openpyxl.styles import Font
            wb = openpyxl.load_workbook(path)
            ws = wb.create_sheet("Heures supp")
            ws.append(["Formateur", "Type", "Heures travaillées / semaine", "Masse statutaire (h/semaine)", "Heures supp / semaine"])
            for c in ws[1]:
                c.font = Font(bold=True)
            for a in res:
                if not a["total"]:
                    continue
                st, hs = self._hs_week(smap, a["nom"], a["total"])
                ws.append([a["nom"], a["type"], round(a["total"] / 4.0, 2), st if st else "", round(hs, 2) if st else ""])
            for col, w in zip("ABCDE", (32, 14, 28, 30, 22)):
                ws.column_dimensions[col].width = w
            wb.save(path)
        except Exception:
            logger.exception("Feuille heures supp")

    # --- ANALYSE : MASSE HORAIRE DES FORMATEURS (lue dans l'emploi du temps) ---
    def show_analysis_result(self):
        """Tableau de la masse horaire de chaque formateur, par jour et par semaine,
        calcule d'apres les seances de l'emploi du temps."""
        self.clear_main_frame()
        D = tt_load_emploi()
        frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        frame.pack(fill="both", expand=True, padx=20, pady=16)
        head = ctk.CTkFrame(frame, fg_color="transparent"); head.pack(fill="x")
        ctk.CTkLabel(head, text="Analyse des emplois du temps", font=ctk.CTkFont(size=24, weight="bold")).pack(side="left")
        ctk.CTkButton(head, text="Emploi du temps", width=130, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=self.show_emploi_module).pack(side="right", padx=4)
        ctk.CTkButton(head, text="Actualiser", width=100, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=self.show_analysis_result).pack(side="right", padx=4)
        ctk.CTkButton(head, text="Par semaine / par mois", width=170, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=self.show_analysis_periods).pack(side="right", padx=4)
        if not D or not D["seances"]:
            ctk.CTkLabel(frame, justify="left", wraplength=850,
                         text="L'emploi du temps ne contient encore aucune séance.\n"
                              "Ouvrez le module Emploi du temps, puis « Importer séances eNote » (ou ajoutez les séances à la main).").pack(anchor="w", pady=20)
            return
        res = tt_analyse(D)
        smap = self._stat_map()
        nb_f = sum(1 for a in res if a["total"])
        nb_s = len(D["seances"])
        ctk.CTkLabel(frame, text=f"Masse horaire travaillée par formateur, par jour et par semaine  —  {nb_f} formateur(s), {nb_s} séance(s)",
                     font=ctk.CTkFont(size=13)).pack(anchor="w", pady=(4, 8))

        st = ttk.Style()
        st.configure("Ana.Treeview", rowheight=26, font=("Segoe UI", 10))
        st.configure("Ana.Treeview.Heading", font=("Segoe UI", 10, "bold"))
        cols = ("formateur", "type") + tuple(f"j{d}" for d in range(6)) + ("total", "stat", "hs", "nb")
        heads = ("Formateur", "Type") + tuple(TT_DAYS) + ("Total / semaine", "Masse statutaire", "H. supp / semaine", "Séances")
        wrap = ttk.Frame(frame); wrap.pack(fill="both", expand=True)
        tv = ttk.Treeview(wrap, columns=cols, show="headings", selectmode="browse", height=12, style="Ana.Treeview")
        sb = ttk.Scrollbar(wrap, orient="vertical", command=tv.yview); tv.configure(yscrollcommand=sb.set)
        for c, hd in zip(cols, heads):
            tv.heading(c, text=hd)
            tv.column(c, width=230 if c == "formateur" else 90 if c == "type" else 120 if c in ("total", "stat") else 130 if c == "hs" else 80,
                      anchor="w" if c == "formateur" else "center")
        tv.pack(side="left", fill="both", expand=True); sb.pack(side="right", fill="y")
        tv.tag_configure("tot", background="#dfe6ee", font=("Segoe UI", 10, "bold"))
        tv.tag_configure("nul", foreground="#999999")
        tv.tag_configure("hs", foreground="#c25b00")
        hh = lambda q: tt_dur_txt(q) if q else "-"

        show_zero = tk.BooleanVar(value=False)
        def fill():
            tv.delete(*tv.get_children())
            tot, nb, ths = [0] * 6, 0, 0.0
            for i, a in enumerate(res):
                if not a["total"] and not show_zero.get():
                    continue
                st, hs = self._hs_week(smap, a["nom"], a["total"])
                tg = ("nul",) if not a["total"] else (("hs",) if hs > 0 else ())
                tv.insert("", "end", iid=str(i), tags=tg,
                          values=[a["nom"], a["type"]] + [hh(q) for q in a["jours"]] +
                                 [hh(a["total"]), ("%g h" % st) if st else "—", ("%g h" % round(hs, 2)) if st else "—", len(a["seances"])])
                tot = [x + y for x, y in zip(tot, a["jours"])]; nb += len(a["seances"]); ths += hs
            tv.insert("", "end", iid="total", tags=("tot",), values=["TOTAL", ""] + [hh(q) for q in tot] + [hh(sum(tot)), "", "%g h" % round(ths, 2), nb])
        fill()
        ctk.CTkCheckBox(frame, text="Afficher aussi les formateurs sans séance", variable=show_zero, command=fill).pack(anchor="w", pady=6)

        lbl = ctk.CTkLabel(frame, text="Sélectionnez un formateur pour voir son tableau détaillé.", font=ctk.CTkFont(size=14, weight="bold"))
        lbl.pack(anchor="w", pady=(6, 4))
        dwrap = ttk.Frame(frame); dwrap.pack(fill="both", expand=True)
        dcols = ("jour", "horaire", "groupe", "module", "espace", "duree")
        dv = ttk.Treeview(dwrap, columns=dcols, show="headings", height=7, style="Ana.Treeview")
        dsb = ttk.Scrollbar(dwrap, orient="vertical", command=dv.yview); dv.configure(yscrollcommand=dsb.set)
        for c, hd, wd in zip(dcols, ("Jour", "Horaire", "Groupe", "Module", "Espace", "Durée"), (110, 140, 120, 280, 120, 90)):
            dv.heading(c, text=hd); dv.column(c, width=wd, anchor="w" if c == "module" else "center")
        dv.pack(side="left", fill="both", expand=True); dsb.pack(side="right", fill="y")
        dv.tag_configure("tot", background="#dfe6ee", font=("Segoe UI", 10, "bold"))

        def detail(_=None):
            dv.delete(*dv.get_children())
            sel = tv.selection()
            if not sel or sel[0] == "total":
                lbl.configure(text="Sélectionnez un formateur pour voir son tableau détaillé.")
                return
            a = res[int(sel[0])]
            st, hs = self._hs_week(smap, a["nom"], a["total"])
            extra = (f"  —  masse statutaire {st:g} h  —  heures supp {round(hs, 2):g} h / semaine") if st else "  —  masse statutaire non renseignée (fiche du formateur)"
            lbl.configure(text=f"{a['nom']}  —  {hh(a['total']) if a['total'] else '0 h'} par semaine{extra}")
            for s in a["seances"]:
                g = tt_get(D, "groupes", s["groupe"]) or {"nom": "?"}
                e = tt_get(D, "espaces", s["espace"]) or {"nom": "?"}
                dv.insert("", "end", values=[TT_DAYS[s["day"]], f"{tt_qt(s['start'])} - {tt_qt(s['start'] + s['dur'])}",
                                             g["nom"], s.get("matiere", ""), e["nom"], tt_dur_txt(s["dur"])])
            for d in range(6):
                if a["jours"][d]:
                    dv.insert("", "end", tags=("tot",), values=[f"Total {TT_DAYS[d]}", "", "", "", "", tt_dur_txt(a["jours"][d])])
            dv.insert("", "end", tags=("tot",), values=["TOTAL SEMAINE", "", "", "", "", hh(a["total"])])
        tv.bind("<<TreeviewSelect>>", detail)

        def exporter():
            p = filedialog.asksaveasfilename(defaultextension=".xlsx", initialfile="Masse_horaire_formateurs.xlsx",
                                             filetypes=[("Excel", "*.xlsx")])
            if not p: return
            try:
                tt_analyse_excel(p, D, res)
                self._append_hs_sheet(p, res, smap)
                messagebox.showinfo("Export Excel", "Fichier enregistré : un résumé + un tableau par formateur + la feuille « Heures supp ».")
            except Exception as ex:
                logger.exception("Export analyse")
                messagebox.showerror("Export Excel", f"Impossible d'enregistrer le fichier :\n{ex}")
        ctk.CTkButton(head, text="Exporter Excel", width=120, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=exporter).pack(side="right", padx=4)

    # --- ANALYSE PAR SEMAINE ET PAR MOIS (emploi du temps type - jours d'absence retires) ---
    _MOIS_FR = ("Janvier", "Février", "Mars", "Avril", "Mai", "Juin", "Juillet", "Août",
                "Septembre", "Octobre", "Novembre", "Décembre")

    def _ana_abs_rows(self):
        """[(mots du nom, motif, date_debut, date_fin)] : toutes les absences enregistrees (lues une seule fois)."""
        rows = []
        try:
            with get_db_connection() as conn:
                cur = conn.cursor()
                cur.execute("SELECT p.nom, p.prenom, a.motif, a.date_debut, a.date_fin FROM absences a JOIN personnel p ON a.personnel_id = p.id")
                data = cur.fetchall()
            for nom, prenom, motif, d1, d2 in data:
                try:
                    rows.append((frozenset(tt_norm(f"{prenom or ''} {nom}").split()), motif,
                                 datetime.strptime(d1, "%d/%m/%Y").date(), datetime.strptime(d2, "%d/%m/%Y").date()))
                except (ValueError, TypeError):
                    pass
        except Exception:
            logger.exception("Lecture des absences impossible (analyse par periode)")
        return rows

    def _ana_week(self, D, res, rows, lundi, cache, per=None):
        """Masse horaire de chaque formateur pour la semaine commencant ce lundi : l'emploi du temps type,
        moins les jours ou le formateur est absent. {nom: {type, jours, theo, total, nb, abs}} (durees en quarts d'heure)."""
        out = {}
        hors = {d for d in range(6) if per and not (per[0] <= lundi + timedelta(days=d) <= per[1])}     # jours hors periode de formation
        for a in res:
            o = next((x for x in D["formateurs"] if tt_fname(x) == a["nom"]), None)
            absd = {}
            if o:
                pre = o.get("prenom", "") or ""
                forms = (tt_fname(o), f"{pre} {o['nom']}", f"{o['nom']} {pre}")
                keys = {frozenset(tt_norm(t).split()) for t in forms}
                names = {tt_norm(t) for t in forms}
                for d in range(6):
                    if d in hors:
                        continue
                    j = lundi + timedelta(days=d)
                    hit = next((m for k, m, d1, d2 in rows if k in keys and d1 <= j <= d2), None)
                    if hit is None:
                        if j not in cache:
                            try:
                                cache[j] = tt_absents(j)
                            except Exception:
                                cache[j] = set()
                        if names & cache[j]:
                            hit = "Absent"
                    if hit:
                        absd[d] = hit
            jours = [0 if (d in absd or d in hors) else q for d, q in enumerate(a["jours"])]
            out[a["nom"]] = {"type": a["type"], "jours": jours, "theo": sum(q for d, q in enumerate(a["jours"]) if d not in hors), "total": sum(jours),
                             "nb": sum(1 for s in a["seances"] if s["day"] not in absd and s["day"] not in hors), "abs": absd}
        return out

    def show_analysis_periods(self):
        """Analyse par semaine (choix de la semaine) et par mois (choix du mois + des semaines a integrer)."""
        D = tt_load_emploi()
        if not D or not D["seances"]:
            return self.show_analysis_result()
        self.clear_main_frame()
        res = [a for a in tt_analyse(D) if a["total"]]
        smap = self._stat_map()
        rows, cache = self._ana_abs_rows(), {}
        hh = lambda q: tt_dur_txt(q) if q else "-"
        heures = lambda q: round(q / 4.0, 2)

        def hsx(nom, q):                       # (masse statutaire, heures supp) pour l'export, "" si masse non renseignee
            st, hs = self._hs_week(smap, nom, q)
            return (st, round(hs, 2)) if st else ("", "")

        def hs_mois(nom, ws):                  # somme des heures supp de chaque semaine retenue
            if not smap.get(self._name_key(nom)):
                return ""
            return round(sum(self._hs_week(smap, nom, w["total"])[1] for w in ws), 2)
        MOIS = self._MOIS_FR
        wnum = lambda lu: "S%d" % lu.isocalendar()[1]
        monday = lambda d: d - timedelta(days=d.weekday())
        today = datetime.now().date()
        sett = self._analysis_settings()
        def _pd(k, dflt):
            try:
                return datetime.strptime(sett.get(k, ""), "%d/%m/%Y").date()
            except (ValueError, TypeError):
                return dflt
        deb, fin = _pd("form_debut", datetime(2026, 9, 7).date()), _pd("form_fin", datetime(2027, 7, 15).date())   # plan de formation
        if fin < deb:
            deb, fin = fin, deb
        per = (deb, fin)
        clamp = lambda d: min(max(d, deb), fin)
        fnum = lambda lu: (lu - monday(deb)).days // 7 + 1          # n° de la semaine dans la formation

        frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        frame.pack(fill="both", expand=True, padx=20, pady=16)
        head = ctk.CTkFrame(frame, fg_color="transparent"); head.pack(fill="x")
        ctk.CTkLabel(head, text="Analyse par semaine et par mois", font=ctk.CTkFont(size=24, weight="bold")).pack(side="left")
        ctk.CTkButton(head, text="Retour", width=100, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=self.show_analysis_result).pack(side="right", padx=4)
        ctk.CTkLabel(frame, font=ctk.CTkFont(size=13), justify="left", wraplength=1000,
                     text="Heures = emploi du temps type, moins les jours où le formateur est absent (absences enregistrées). "
                          "Heures supp = heures travaillées au-delà de la masse statutaire hebdomadaire (fiche du formateur).").pack(anchor="w", pady=(4, 8))

        pbar = ttk.Frame(frame); pbar.pack(fill="x", pady=(0, 8))
        ttk.Label(pbar, text="Plan de formation  —  début :", font=("Segoe UI", 10, "bold")).pack(side="left", padx=(0, 6))
        de_deb = DateEntry(pbar, date_pattern="dd/mm/yyyy", width=11, background=MAIN_COLOR, foreground="white", borderwidth=2)
        de_deb.pack(side="left"); de_deb.set_date(deb)
        ttk.Label(pbar, text="fin :", font=("Segoe UI", 10, "bold")).pack(side="left", padx=(12, 6))
        de_fin = DateEntry(pbar, date_pattern="dd/mm/yyyy", width=11, background=MAIN_COLOR, foreground="white", borderwidth=2)
        de_fin.pack(side="left"); de_fin.set_date(fin)
        def appliquer():
            a, b = de_deb.get_date(), de_fin.get_date()
            if b < a:
                return messagebox.showwarning("Plan de formation", "La date de fin doit être après la date de début.")
            sett2 = self._analysis_settings(); sett2["form_debut"], sett2["form_fin"] = a.strftime("%d/%m/%Y"), b.strftime("%d/%m/%Y")
            self._save_analysis_settings(sett2); self.show_analysis_periods()
        ttk.Button(pbar, text="Appliquer", command=appliquer).pack(side="left", padx=10)
        ttk.Label(pbar, foreground="#555555", text="%d semaine(s) de formation" % fnum(monday(fin))).pack(side="left", padx=6)

        st = ttk.Style()
        st.configure("Ana.Treeview", rowheight=26, font=("Segoe UI", 10))
        st.configure("Ana.Treeview.Heading", font=("Segoe UI", 10, "bold"))
        nb = ttk.Notebook(frame); nb.pack(fill="both", expand=True)
        tabw, tabm = ttk.Frame(nb), ttk.Frame(nb)
        nb.add(tabw, text="  Par semaine  "); nb.add(tabm, text="  Par mois  ")

        # ------------------------------------------------------------ PAR SEMAINE
        cur = {"lundi": monday(clamp(today))}
        bar = ttk.Frame(tabw); bar.pack(fill="x", pady=8, padx=4)
        ttk.Label(bar, text="Semaine du :", font=("Segoe UI", 10, "bold")).pack(side="left", padx=(0, 6))
        btn_prev = tk.Button(bar, text="\u25C0", relief="flat", bg="#ffffff", bd=1, padx=8, cursor="hand2")
        de = DateEntry(bar, date_pattern="dd/mm/yyyy", width=11, background=MAIN_COLOR, foreground="white", borderwidth=2)
        btn_next = tk.Button(bar, text="\u25B6", relief="flat", bg="#ffffff", bd=1, padx=8, cursor="hand2")
        btn_prev.pack(side="left"); de.pack(side="left", padx=3); btn_next.pack(side="left")
        lbl_sem = ttk.Label(bar, font=("Segoe UI", 11, "bold")); lbl_sem.pack(side="left", padx=14)

        wcols = ("formateur", "type") + tuple(f"j{d}" for d in range(6)) + ("total", "stat", "hs", "nb", "abs")
        wheads = ("Formateur", "Type") + tuple(TT_DAYS) + ("Total semaine", "Masse statutaire", "H. supp", "Séances", "Absences")
        wwrap = ttk.Frame(tabw); wwrap.pack(fill="both", expand=True, padx=4, pady=(0, 6))
        tv = ttk.Treeview(wwrap, columns=wcols, show="headings", height=14, style="Ana.Treeview")
        wsb = ttk.Scrollbar(wwrap, orient="vertical", command=tv.yview); tv.configure(yscrollcommand=wsb.set)
        for c, hd in zip(wcols, wheads):
            tv.heading(c, text=hd)
            tv.column(c, width=210 if c == "formateur" else 90 if c == "type" else 130 if c == "total" else 260 if c == "abs" else 115 if c in ("stat", "hs") else 75,
                      anchor="w" if c in ("formateur", "abs") else "center")
        tv.pack(side="left", fill="both", expand=True); wsb.pack(side="right", fill="y")
        tv.tag_configure("tot", background="#dfe6ee", font=("Segoe UI", 10, "bold"))
        tv.tag_configure("abs", foreground="#b3261e")
        tv.tag_configure("hs", foreground="#c25b00")

        def week_rows(lu):
            W = self._ana_week(D, res, rows, lu, cache, per)
            return [(a["nom"], W[a["nom"]]) for a in res]

        def fill_w(delta=0, *_):
            if delta:
                cur["lundi"] += timedelta(days=7 * delta)
            else:
                cur["lundi"] = monday(de.get_date())
            cur["lundi"] = min(max(cur["lundi"], monday(deb)), monday(fin))        # on reste dans le plan de formation
            lu = cur["lundi"]; de.set_date(lu)
            lbl_sem.configure(text="Semaine %d de la formation  (%s)   du %s au %s" % (fnum(lu), wnum(lu), lu.strftime("%d/%m/%Y"), (lu + timedelta(days=5)).strftime("%d/%m/%Y")))
            tv.delete(*tv.get_children())
            tot, n, ths = [0] * 6, 0, 0.0
            for nom, w in week_rows(lu):
                if not w["total"] and not w["abs"]:
                    continue
                txt = ", ".join("%s. (%s)" % (TT_DAYS[d][:3], m) for d, m in sorted(w["abs"].items()))
                st, hs = self._hs_week(smap, nom, w["total"])
                tv.insert("", "end", tags=("abs",) if w["abs"] else (("hs",) if hs > 0 else ()),
                          values=[nom, w["type"]] + [hh(q) for q in w["jours"]] +
                                 [hh(w["total"]), ("%g h" % st) if st else "—", ("%g h" % round(hs, 2)) if st else "—", w["nb"], txt])
                tot = [x + y for x, y in zip(tot, w["jours"])]; n += w["nb"]; ths += hs
            tv.insert("", "end", tags=("tot",), values=["TOTAL", ""] + [hh(q) for q in tot] + [hh(sum(tot)), "", "%g h" % round(ths, 2), n, ""])
        btn_prev.configure(command=lambda: fill_w(-1)); btn_next.configure(command=lambda: fill_w(1))
        de.bind("<<DateEntrySelected>>", lambda e: fill_w(0))
        de.set_date(cur["lundi"]); fill_w(0)

        # ------------------------------------------------------------ PAR MOIS
        mbar = ttk.Frame(tabm); mbar.pack(fill="x", pady=8, padx=4)
        ttk.Label(mbar, text="Mois :", font=("Segoe UI", 10, "bold")).pack(side="left", padx=(0, 6))
        cbm = ttk.Combobox(mbar, values=MOIS, state="readonly", width=12); cbm.pack(side="left"); cbm.current(clamp(today).month - 1)
        ttk.Label(mbar, text="Année :", font=("Segoe UI", 10, "bold")).pack(side="left", padx=(14, 6))
        cby = ttk.Combobox(mbar, values=[str(y) for y in range(deb.year, fin.year + 1)], state="readonly", width=6)
        cby.pack(side="left"); cby.set(str(clamp(today).year))

        wk_box = ttk.LabelFrame(tabm, text=" Semaines à intégrer dans ce mois (cochez / décochez) ")
        wk_box.pack(fill="x", padx=4, pady=(0, 6))
        wk_inner = ttk.Frame(wk_box); wk_inner.pack(fill="x", padx=8, pady=4)
        ttk.Label(wk_box, foreground="#555555",
                  text="Par défaut, une semaine est rattachée au mois qui contient son jeudi (chaque semaine compte ainsi dans un seul mois).").pack(anchor="w", padx=8, pady=(0, 6))
        wvars = []
        lbl_mois = ttk.Label(tabm, font=("Segoe UI", 11, "bold")); lbl_mois.pack(anchor="w", padx=4, pady=(0, 4))
        mwrap = ttk.Frame(tabm); mwrap.pack(fill="both", expand=True, padx=4, pady=(0, 6))
        mv = ttk.Treeview(mwrap, show="headings", height=10, style="Ana.Treeview")
        msb = ttk.Scrollbar(mwrap, orient="vertical", command=mv.yview); mv.configure(yscrollcommand=msb.set)
        mv.pack(side="left", fill="both", expand=True); msb.pack(side="right", fill="y")
        mv.tag_configure("tot", background="#dfe6ee", font=("Segoe UI", 10, "bold"))
        mv.tag_configure("hs", foreground="#c25b00")
        mstate = {"sel": []}

        def month_info():
            m, y = cbm.current() + 1, int(cby.get())
            first = datetime(y, m, 1).date()
            last = datetime(y + (m == 12), m % 12 + 1, 1).date() - timedelta(days=1)
            lus, lu = [], monday(first)
            while lu <= last:
                if lu + timedelta(days=5) >= deb and lu <= fin:                    # seulement les semaines de la formation
                    lus.append(lu)
                lu += timedelta(days=7)
            return m, y, lus

        def fill_m(*_):
            sel = [lu for lu, v in wvars if v.get()]
            mstate["sel"] = sel
            m, y = cbm.current() + 1, int(cby.get())
            cols = ("formateur", "type") + tuple(f"w{i}" for i in range(len(sel))) + ("total", "perdu", "hs", "nb")
            mv.configure(columns=cols, displaycolumns=cols)
            mv.heading("formateur", text="Formateur"); mv.column("formateur", width=220, anchor="w")
            mv.heading("type", text="Type"); mv.column("type", width=90, anchor="center")
            for i, lu in enumerate(sel):
                mv.heading(f"w{i}", text="%s (%s)" % (wnum(lu), lu.strftime("%d/%m"))); mv.column(f"w{i}", width=95, anchor="center")
            mv.heading("total", text="Total mois"); mv.column("total", width=110, anchor="center")
            mv.heading("perdu", text="Perdu (absences)"); mv.column("perdu", width=130, anchor="center")
            mv.heading("hs", text="Heures supp"); mv.column("hs", width=110, anchor="center")
            mv.heading("nb", text="Séances"); mv.column("nb", width=80, anchor="center")
            mv.delete(*mv.get_children())
            weeks = [dict(week_rows(lu)) for lu in sel]
            wt, T, P, N, H = [0] * len(sel), 0, 0, 0, 0.0
            for a in res:
                ws = [w[a["nom"]] for w in weeks]
                tot, perdu, n = sum(w["total"] for w in ws), sum(w["theo"] - w["total"] for w in ws), sum(w["nb"] for w in ws)
                if not tot and not perdu:
                    continue
                hsm = hs_mois(a["nom"], ws)
                mv.insert("", "end", tags=(("hs",) if hsm not in ("", 0) else ()),
                          values=[a["nom"], a["type"]] + [hh(w["total"]) for w in ws] + [hh(tot), hh(perdu), ("%g h" % hsm) if hsm != "" else "—", n])
                wt = [x + w["total"] for x, w in zip(wt, ws)]; T += tot; P += perdu; N += n; H += hsm or 0
            mv.insert("", "end", tags=("tot",), values=["TOTAL", ""] + [hh(x) for x in wt] + [hh(T), hh(P), "%g h" % round(H, 2), N])
            lbl_mois.configure(text="%s %d  —  %d semaine(s) intégrée(s)  —  %s" % (MOIS[m - 1], y, len(sel), hh(T) if T else "0 h"))

        def build_weeks(*_):
            for w in wk_inner.winfo_children():
                w.destroy()
            wvars.clear()
            m, y, lus = month_info()
            for i, lu in enumerate(lus):
                jeudi = lu + timedelta(days=3)
                dans = sum(1 for d in range(6) if (lu + timedelta(days=d)).month == m and (lu + timedelta(days=d)).year == y)
                defaut = jeudi.month == m and jeudi.year == y
                dans = sum(1 for d in range(6) if (lu + timedelta(days=d)).month == m and (lu + timedelta(days=d)).year == y and deb <= lu + timedelta(days=d) <= fin)
                txt = "Sem. %d (%s)   du %s au %s   (%d jour(s) dans %s)" % (fnum(lu), wnum(lu), lu.strftime("%d/%m"), (lu + timedelta(days=5)).strftime("%d/%m"), dans, MOIS[m - 1].lower())
                if not defaut:
                    txt += "   — rattachée à %s" % MOIS[jeudi.month - 1].lower()
                v = tk.BooleanVar(value=defaut); wvars.append((lu, v))
                ttk.Checkbutton(wk_inner, text=txt, variable=v, command=fill_m).grid(row=i // 2, column=i % 2, sticky="w", padx=(0, 30), pady=1)
            fill_m()
        cbm.bind("<<ComboboxSelected>>", build_weeks); cby.bind("<<ComboboxSelected>>", build_weeks)
        build_weeks()

        # ------------------------------------------------------------ EXPORT EXCEL
        def exporter():
            mois_tab = nb.index(nb.select()) == 1
            if mois_tab:
                m, y = cbm.current() + 1, int(cby.get())
                init = "Masse_horaire_%s_%d.xlsx" % (MOIS[m - 1], y)
            else:
                init = "Masse_horaire_%s.xlsx" % cur["lundi"].strftime("%d-%m-%Y")
            p = filedialog.asksaveasfilename(defaultextension=".xlsx", initialfile=init, filetypes=[("Excel", "*.xlsx")])
            if not p:
                return
            try:
                JOURS = list(TT_DAYS)
                def week_df(lu):
                    return pd.DataFrame([[nom, w["type"]] + [heures(q) for q in w["jours"]] + [heures(w["total"])] + list(hsx(nom, w["total"])) + [w["nb"],
                                          ", ".join("%s (%s)" % (TT_DAYS[d][:3], mo) for d, mo in sorted(w["abs"].items()))]
                                         for nom, w in week_rows(lu) if w["total"] or w["abs"]],
                                        columns=["Formateur", "Type"] + JOURS + ["Total (h)", "Masse statutaire (h)", "Heures supp (h)", "Séances", "Absences"])
                with pd.ExcelWriter(p) as xw:
                    if not mois_tab:
                        week_df(cur["lundi"]).to_excel(xw, sheet_name=("%s_%s" % (wnum(cur["lundi"]), cur["lundi"].strftime("%d-%m-%Y")))[:31], index=False)
                    else:
                        sel = mstate["sel"]; weeks = [dict(week_rows(lu)) for lu in sel]; rec = []
                        for a in res:
                            ws = [w[a["nom"]] for w in weeks]
                            tot, perdu = sum(w["total"] for w in ws), sum(w["theo"] - w["total"] for w in ws)
                            if tot or perdu:
                                rec.append([a["nom"], a["type"]] + [heures(w["total"]) for w in ws] + [heures(tot), heures(perdu), hs_mois(a["nom"], ws), sum(w["nb"] for w in ws)])
                        pd.DataFrame(rec, columns=["Formateur", "Type"] + ["%s (%s)" % (wnum(lu), lu.strftime("%d/%m")) for lu in sel]
                                     + ["Total mois (h)", "Perdu absences (h)", "Heures supp (h)", "Séances"]).to_excel(xw, sheet_name="Récap %s %d" % (MOIS[m - 1], y), index=False)
                        for lu in sel:
                            week_df(lu).to_excel(xw, sheet_name=("%s_%s" % (wnum(lu), lu.strftime("%d-%m-%Y")))[:31], index=False)
                messagebox.showinfo("Export Excel", "Fichier enregistré.")
            except Exception as ex:
                logger.exception("Export analyse par periode")
                messagebox.showerror("Export Excel", "Impossible d'enregistrer le fichier :\n%s" % ex)
        ctk.CTkButton(head, text="Exporter Excel", width=120, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=exporter).pack(side="right", padx=4)

    # --- ANALYSE DES EMPLOIS DU TEMPS ---
    def _analysis_settings(self):
        """Charge les réglages de l'analyse automatique."""
        default = {"enabled": True, "last_run": ""}
        try:
            with open(ANALYSIS_SETTINGS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            return {**default, **data}
        except (OSError, json.JSONDecodeError):
            return default

    def _save_analysis_settings(self, settings):
        try:
            atomic_write_json(ANALYSIS_SETTINGS_FILE, settings, indent=2)
        except OSError:
            logger.exception("Impossible d'enregistrer les réglages de l'analyse")

    def set_auto_analysis(self):
        settings = self._analysis_settings()
        settings["enabled"] = bool(self.auto_analysis_var.get())
        self._save_analysis_settings(settings)
        if hasattr(self, "analysis_status_label"):
            self.analysis_status_label.configure(
                text="Activée : chaque lundi à 10:00 (application ouverte)."
                if settings["enabled"] else
                "Désactivée : l’analyse peut toujours être lancée manuellement."
            )

    def run_analysis_now(self):
        """Affiche la masse horaire de chaque formateur (calculee d'apres l'emploi du temps)."""
        self.show_analysis_result()

    # --- ANALYSE PAR SEMAINE A PARTIR DE FICHIERS EXCEL IMPORTES ---
    @staticmethod
    def _hm_to_hours(v):
        """Heure Excel ou texte (time, datetime, '08:30', '8h30') -> heures decimales, ou None."""
        if v is None:
            return None
        if hasattr(v, "hour") and hasattr(v, "minute"):
            return v.hour + v.minute / 60.0
        m = re.match(r"\s*(\d{1,2})\s*[:hH]\s*(\d{0,2})", str(v))
        if m:
            return int(m.group(1)) + int(m.group(2) or 0) / 60.0
        return None

    def _read_analysis_file(self, path):
        """Lit un export Excel/CSV (colonnes Date, H.D, H.F, Durée en H, Formateur facultatif...)
        et renvoie la liste des seances : {formateur, date, h}."""
        base = os.path.splitext(os.path.basename(path))[0].replace("_", " ").replace("-", " ").strip()
        if path.lower().endswith(".csv"):
            raw = pd.read_csv(path, header=None, dtype=object, sep=None, engine="python")
        else:
            raw = pd.read_excel(path, header=None, dtype=object)
        # ligne d'en-tete = celle qui contient "date" et une colonne d'heures
        hdr = None
        for i in range(min(len(raw), 30)):
            vals = [_fnorm(v) for v in raw.iloc[i].tolist()]
            if "date" in vals and any(v in ("h d", "h f", "duree en h", "duree hh mm") for v in vals):
                hdr = i
                break
        if hdr is None:
            raise ValueError("colonnes « Date » et « H.D / H.F » introuvables")
        cols = {}
        for j, v in enumerate(raw.iloc[hdr].tolist()):
            cols.setdefault(_fnorm(v), j)
        c_date, c_hd, c_hf = cols.get("date"), cols.get("h d"), cols.get("h f")
        c_dur, c_form = cols.get("duree en h"), cols.get("formateur")
        out = []
        for _, row in raw.iloc[hdr + 1:].iterrows():
            dv = row.iloc[c_date]
            iso = isinstance(dv, str) and _ISO_RE.match(dv.strip())
            d = pd.to_datetime(dv, dayfirst=not iso, errors="coerce")   # aaaa-mm-jj lu tel quel, jj/mm/aaaa en jour d'abord
            if pd.isna(d):
                continue
            h = None
            if c_dur is not None:
                try:
                    h = float(str(row.iloc[c_dur]).replace(",", "."))
                except ValueError:
                    h = None
            if h is None or h != h or h <= 0:
                a = self._hm_to_hours(row.iloc[c_hd]) if c_hd is not None else None
                b = self._hm_to_hours(row.iloc[c_hf]) if c_hf is not None else None
                if a is None or b is None or b <= a:
                    continue
                h = b - a
            f = _cell_txt(row.iloc[c_form]) if c_form is not None else ""
            out.append({"formateur": f or base, "date": d.date(), "h": h})
        return out

    def import_analysis_files(self):
        """Importe un ou plusieurs fichiers Excel et affiche la masse horaire par semaine."""
        paths = filedialog.askopenfilenames(
            parent=self.winfo_toplevel(), title="Fichiers Excel des emplois du temps (plusieurs possibles)",
            filetypes=[("Excel / CSV", "*.xlsx *.xls *.csv"), ("Tous les fichiers", "*.*")])
        if not paths:
            return
        entries, erreurs = [], []
        for p in paths:
            try:
                lot = self._read_analysis_file(p)
            except Exception as ex:
                erreurs.append(f"{os.path.basename(p)} : {ex}")
                continue
            if not lot:
                erreurs.append(f"{os.path.basename(p)} : aucune séance trouvée")
                continue
            entries.extend(lot)
        if not entries:
            return messagebox.showerror("Import Excel", "Aucun fichier exploitable.\n\n" + "\n".join(erreurs))
        self.show_import_analysis(entries, erreurs)

    def show_import_analysis(self, entries, erreurs=()):
        """Masse horaire par formateur : un tableau par semaine + recapitulatif de toutes les semaines."""
        self.clear_main_frame()
        JOURS = ("Lun", "Mar", "Mer", "Jeu", "Ven", "Sam", "Dim")
        hh = lambda h: "-" if not h else "%dh%02d" % divmod(int(round(h * 60)), 60)

        data, nbs = {}, {}
        for e in entries:
            lu = e["date"] - timedelta(days=e["date"].weekday())
            data.setdefault(lu, {}).setdefault(e["formateur"], [0.0] * 7)[e["date"].weekday()] += e["h"]
            nbs[(lu, e["formateur"])] = nbs.get((lu, e["formateur"]), 0) + 1
        semaines = sorted(data)
        formateurs = sorted({f for w in data.values() for f in w}, key=_fnorm)
        wnum = lambda lu: "S%d" % lu.isocalendar()[1]
        wlabel = lambda lu: "%s  du %s au %s" % (wnum(lu), lu.strftime("%d/%m/%Y"), (lu + timedelta(days=5)).strftime("%d/%m/%Y"))

        frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        frame.pack(fill="both", expand=True, padx=20, pady=16)
        head = ctk.CTkFrame(frame, fg_color="transparent"); head.pack(fill="x")
        ctk.CTkLabel(head, text="Analyse par semaine (fichiers importés)", font=ctk.CTkFont(size=24, weight="bold")).pack(side="left")
        ctk.CTkButton(head, text="Retour", width=100, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=self.show_analysis).pack(side="right", padx=4)
        ctk.CTkLabel(frame, font=ctk.CTkFont(size=13),
                     text=f"{len(entries)} séance(s)  —  {len(formateurs)} formateur(s)  —  {len(semaines)} semaine(s)").pack(anchor="w", pady=(4, 8))

        st = ttk.Style()
        st.configure("Ana.Treeview", rowheight=26, font=("Segoe UI", 10))
        st.configure("Ana.Treeview.Heading", font=("Segoe UI", 10, "bold"))

        # --- tableau de la semaine choisie ---
        bar = ctk.CTkFrame(frame, fg_color="transparent"); bar.pack(fill="x")
        ctk.CTkLabel(bar, text="Semaine :", font=ctk.CTkFont(size=14, weight="bold")).pack(side="left", padx=(0, 8))
        cb = ttk.Combobox(bar, values=[wlabel(lu) for lu in semaines], state="readonly", width=44)
        cb.pack(side="left"); cb.current(0)

        cols = ("formateur",) + tuple(f"j{d}" for d in range(7)) + ("total", "nb")
        heads = ("Formateur",) + JOURS + ("Total semaine", "Séances")
        wrap = ttk.Frame(frame); wrap.pack(fill="both", expand=True, pady=(6, 8))
        tv = ttk.Treeview(wrap, columns=cols, show="headings", height=9, style="Ana.Treeview")
        sb = ttk.Scrollbar(wrap, orient="vertical", command=tv.yview); tv.configure(yscrollcommand=sb.set)
        for c, hd in zip(cols, heads):
            tv.heading(c, text=hd)
            tv.column(c, width=230 if c == "formateur" else 120 if c == "total" else 80, anchor="w" if c == "formateur" else "center")
        tv.pack(side="left", fill="both", expand=True); sb.pack(side="right", fill="y")
        tv.tag_configure("tot", background="#dfe6ee", font=("Segoe UI", 10, "bold"))

        def fill_week(_=None):
            lu = semaines[cb.current()]
            tv.delete(*tv.get_children())
            tot, nb = [0.0] * 7, 0
            for f in formateurs:
                if f not in data[lu]:
                    continue
                j = data[lu][f]
                tv.insert("", "end", values=[f] + [hh(x) for x in j] + [hh(sum(j)), nbs[(lu, f)]])
                tot = [a + b for a, b in zip(tot, j)]; nb += nbs[(lu, f)]
            tv.insert("", "end", tags=("tot",), values=["TOTAL"] + [hh(x) for x in tot] + [hh(sum(tot)), nb])
        cb.bind("<<ComboboxSelected>>", fill_week)
        fill_week()

        # --- recapitulatif de toutes les semaines ---
        ctk.CTkLabel(frame, text="Récapitulatif : total d'heures par formateur et par semaine",
                     font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w", pady=(6, 4))
        rcols = ("formateur",) + tuple(f"w{i}" for i in range(len(semaines))) + ("total",)
        rwrap = ttk.Frame(frame); rwrap.pack(fill="both", expand=True)
        rv = ttk.Treeview(rwrap, columns=rcols, show="headings", height=7, style="Ana.Treeview")
        rsb = ttk.Scrollbar(rwrap, orient="vertical", command=rv.yview); rv.configure(yscrollcommand=rsb.set)
        rv.heading("formateur", text="Formateur"); rv.column("formateur", width=230, anchor="w")
        for i, lu in enumerate(semaines):
            rv.heading(f"w{i}", text=f"{wnum(lu)} ({lu.strftime('%d/%m')})"); rv.column(f"w{i}", width=95, anchor="center")
        rv.heading("total", text="Total"); rv.column("total", width=100, anchor="center")
        rv.pack(side="left", fill="both", expand=True); rsb.pack(side="right", fill="y")
        rv.tag_configure("tot", background="#dfe6ee", font=("Segoe UI", 10, "bold"))
        wtot = [0.0] * len(semaines)
        for f in formateurs:
            hs = [sum(data[lu].get(f, [0.0])) for lu in semaines]
            wtot = [a + b for a, b in zip(wtot, hs)]
            rv.insert("", "end", values=[f] + [hh(x) for x in hs] + [hh(sum(hs))])
        rv.insert("", "end", tags=("tot",), values=["TOTAL"] + [hh(x) for x in wtot] + [hh(sum(wtot))])

        def exporter():
            p = filedialog.asksaveasfilename(defaultextension=".xlsx", initialfile="Masse_horaire_par_semaine.xlsx",
                                             filetypes=[("Excel", "*.xlsx")])
            if not p:
                return
            try:
                with pd.ExcelWriter(p) as xw:
                    rec = pd.DataFrame(
                        [[f] + [round(sum(data[lu].get(f, [0.0])), 2) for lu in semaines]
                         + [round(sum(sum(data[lu].get(f, [0.0])) for lu in semaines), 2)] for f in formateurs],
                        columns=["Formateur"] + [wlabel(lu) for lu in semaines] + ["Total (h)"])
                    rec.to_excel(xw, sheet_name="Récapitulatif", index=False)
                    for lu in semaines:
                        rows = [[f] + [round(x, 2) for x in data[lu][f]] + [round(sum(data[lu][f]), 2), nbs[(lu, f)]]
                                for f in formateurs if f in data[lu]]
                        pd.DataFrame(rows, columns=["Formateur"] + list(JOURS) + ["Total (h)", "Séances"]).to_excel(
                            xw, sheet_name=f"{wnum(lu)}_{lu.strftime('%d-%m-%Y')}"[:31], index=False)
                messagebox.showinfo("Export Excel", "Fichier enregistré : un récapitulatif + un onglet par semaine.")
            except Exception as ex:
                logger.exception("Export analyse par semaine")
                messagebox.showerror("Export Excel", f"Impossible d'enregistrer le fichier :\n{ex}")
        ctk.CTkButton(head, text="Exporter Excel", width=120, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                      command=exporter).pack(side="right", padx=4)

        if erreurs:
            messagebox.showwarning("Import Excel", "Fichiers ignorés :\n- " + "\n- ".join(erreurs[:10]))

    def check_scheduled_analysis(self):
        """Lance une fois l'analyse le lundi à partir de 10 h si elle est activée."""
        try:
            settings = self._analysis_settings()
            now = datetime.now()
            today = now.strftime("%Y-%m-%d")
            if settings.get("enabled") and now.weekday() == 0 and now.hour >= 10 and settings.get("last_run") != today:
                settings["last_run"] = today
                self._save_analysis_settings(settings)
                self.show_analysis_result()
        except Exception:
            logger.exception("Erreur lors du contrôle de l'analyse automatique")
        finally:
            if self.winfo_exists():
                self.after(60000, self.check_scheduled_analysis)

    # ======================================================================
    # MODULE TABLEAU DE SERVICE
    # Import du fichier Excel DRIF (Exercice, Secteur, Filiere, Module,
    # MHP/MHT S1-S2, EFM, Operation, Groupe, Mle, Formateur...) puis
    # affectation de chaque module a un formateur choisi (Personnel ou
    # Vacataires). Les affectations sont conservees dans la base.
    # ======================================================================
    TS_DB_COLS = ["exercice", "code_secteur_groupe", "secteur_groupe", "code_secteur", "secteur",
                  "niveau", "type_formation", "creneau", "code_filiere_drif", "intitule_filiere_drif",
                  "code_tc_carte", "code_filiere_carte", "filiere", "filiere_ar", "annee_formation",
                  "code_module", "module", "module_ar", "mhp_s1", "mhsyn_s1", "mhasyn_s1", "mhd_s1",
                  "mht_s1", "mhp_s2", "mhsyn_s2", "mhasyn_s2", "mhd_s2", "mht_s2", "mhp_totale",
                  "mhd_totale", "mh_stage", "mht", "coef", "efm_regional", "operation", "groupe",
                  "mle", "formateur", "affectation"]

    # (en-tete Excel normalise, colonne base, libelle d'affichage)
    TS_COLS = [
        ("exercice", "exercice", "Exercice"),
        ("code secteur groupe", "code_secteur_groupe", "Code Secteur groupé"),
        ("secteur groupe", "secteur_groupe", "Secteur groupé"),
        ("code secteur", "code_secteur", "Code Secteur"),
        ("secteur", "secteur", "Secteur"),
        ("niveau de formation", "niveau", "Niveau de formation"),
        ("type de formation", "type_formation", "Type de formation"),
        ("creneau", "creneau", "Créneau"),
        ("code filiere drif", "code_filiere_drif", "Code Filière DRIF"),
        ("intitule filiere drif", "intitule_filiere_drif", "Intitulé Filière DRIF"),
        ("code tc carte", "code_tc_carte", "Code TC carte"),
        ("code filiere carte", "code_filiere_carte", "Code Filière Carte"),
        ("filiere", "filiere", "Filière"),
        ("lib filiere arabe", "filiere_ar", "Lib Filière Arabe"),
        ("annee de formation", "annee_formation", "Année de Formation"),
        ("code module", "code_module", "Code Module"),
        ("module", "module", "Module"),
        ("module (ar)", "module_ar", "Module (AR)"),
        ("mhp s1", "mhp_s1", "MHP S1"),
        ("mhsyn s1", "mhsyn_s1", "MHSYN S1"),
        ("mhasyn s1", "mhasyn_s1", "MHASYN S1"),
        ("mhd s1", "mhd_s1", "MHD S1"),
        ("mht s1", "mht_s1", "MHT S1"),
        ("mhp s2", "mhp_s2", "MHP S2"),
        ("mhsyn s2", "mhsyn_s2", "MHSYN S2"),
        ("mhasyn s2", "mhasyn_s2", "MHASYN S2"),
        ("mhd s2", "mhd_s2", "MHD S2"),
        ("mht s2", "mht_s2", "MHT S2"),
        ("mhp totale", "mhp_totale", "MHP Totale"),
        ("mhd totale", "mhd_totale", "MHD Totale"),
        ("mh stage", "mh_stage", "MH Stage"),
        ("mht", "mht", "MHT"),
        ("coef", "coef", "Coef"),
        ("efm regional", "efm_regional", "EFM Régional"),
        ("operation", "operation", "Opération"),
        ("groupe", "groupe", "Groupe"),
        ("mle", "mle", "Mle"),
        ("nom & prenom du formateur", "formateur", "Nom & Prénom du Formateur"),
        ("nom et prenom du formateur", "formateur", "Nom & Prénom du Formateur"),
        ("nom & prenom", "formateur", "Nom & Prénom du Formateur"),
        ("nom et prenom", "formateur", "Nom & Prénom du Formateur"),
        ("nom complet", "formateur", "Nom & Prénom du Formateur"),
    ]

    TS_COMPLEXE = "CF BERKANE/ISTA AHFIR"

    @staticmethod
    def _ts_norm(s):
        import unicodedata
        return " ".join(unicodedata.normalize("NFKD", str(s or "")).encode("ascii", "ignore")
                        .decode().casefold().split())

    # ---------------- PAGE ----------------
    def show_tableau_service(self):
        self.clear_main_frame()

        top = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        top.pack(fill="x", padx=20, pady=10)
        ctk.CTkLabel(top, text="Tableau de service — Affectation des modules aux formateurs",
                     font=ctk.CTkFont(size=20, weight="bold")).pack(side="left")
        ctk.CTkButton(top, text="📤  Exporter Excel", fg_color="#217346", hover_color="#145a30",
                      command=self.export_tableau_service).pack(side="right", padx=4)
        ctk.CTkButton(top, text="📥  Importer Excel (DRIF)", fg_color="#217346", hover_color="#145a30",
                      command=self.import_tableau_service).pack(side="right", padx=4)

        self.lbl_ts_stats = ctk.CTkLabel(self.main_frame, text="", font=ctk.CTkFont(size=12, weight="bold"),
                                         text_color="#6b7a89")
        self.lbl_ts_stats.pack(anchor="w", padx=22, pady=(0, 4))

        # --- barre d'affectation ---
        aff = ctk.CTkFrame(self.main_frame, corner_radius=10)
        aff.pack(fill="x", padx=20, pady=4)
        ctk.CTkLabel(aff, text="Affecter la sélection à :", font=ctk.CTkFont(weight="bold")).pack(side="left", padx=(15, 8), pady=10)
        self.combo_ts_aff = ctk.CTkComboBox(aff, values=["—"], width=300,
                                            fg_color=("white", "#343638"),
                                            button_color=MAIN_COLOR, button_hover_color=MAIN_COLOR_HOVER, corner_radius=8)
        self.combo_ts_aff.pack(side="left", padx=4)
        ctk.CTkButton(aff, text="✔  Affecter", fg_color="#1b8a5a", hover_color="#0f5c3a",
                      command=self.ts_affecter).pack(side="left", padx=8)
        ctk.CTkButton(aff, text="✖  Retirer", fg_color="#a83232", hover_color="#7e2424",
                      command=self.ts_desaffecter).pack(side="left", padx=4)
        ctk.CTkButton(aff, text="📋  TDS", fg_color="#8a5a2b", hover_color="#6d4520",
                      command=self.generer_tds_officiel).pack(side="left", padx=(10, 4))
        ctk.CTkButton(aff, text="👥  TDS par formateur", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER,
                      command=self.show_tds).pack(side="left", padx=4)
        ctk.CTkLabel(aff, text="Ctrl+clic : sélection multiple · Double-clic sur une ligne : affecter",
                     font=ctk.CTkFont(size=11), text_color="#6b7a89").pack(side="right", padx=15)

        # --- filtres ---
        filt = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        filt.pack(fill="x", padx=20, pady=(6, 0))
        self.ts_search = ctk.CTkEntry(filt, placeholder_text="Rechercher (module, filière, groupe, formateur)...", width=340)
        self.ts_search.pack(side="left", padx=(0, 8))
        self.ts_search.bind("<KeyRelease>", lambda _e: self.load_tableau_service())
        self.ts_filt_filiere = ctk.CTkComboBox(filt, values=["Toutes les filières"], width=250,
                                               command=lambda _e: self.load_tableau_service())
        self.ts_filt_filiere.pack(side="left", padx=4)
        self.ts_filt_groupe = ctk.CTkComboBox(filt, values=["Tous les groupes"], width=170,
                                              command=lambda _e: self.load_tableau_service())
        self.ts_filt_groupe.pack(side="left", padx=4)
        self.ts_only_free = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(filt, text="Non affectés uniquement", variable=self.ts_only_free,
                        command=self.load_tableau_service).pack(side="left", padx=10)

        # --- tableau ---
        wrap = ctk.CTkFrame(self.main_frame)
        wrap.pack(fill="both", expand=True, padx=20, pady=8)
        cols = ("id", "groupe", "filiere", "creneau", "module", "mhp", "mhd", "mht", "affectation")
        heads = {"id": "N°", "groupe": "Groupe", "filiere": "Filière", "creneau": "Créneau",
                 "module": "Module", "mhp": "MHP", "mhd": "MHD", "mht": "MHT",
                 "affectation": "Affectation"}
        widths = {"id": 50, "groupe": 90, "filiere": 200, "creneau": 90, "module": 300, "mhp": 70,
                  "mhd": 70, "mht": 70, "affectation": 250}
        self.tree_ts = ttk.Treeview(wrap, columns=cols, show="headings", selectmode="extended")
        vsb = ttk.Scrollbar(wrap, orient="vertical", command=self.tree_ts.yview)
        hsb = ttk.Scrollbar(wrap, orient="horizontal", command=self.tree_ts.xview)
        self.tree_ts.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        for c in cols:
            self.tree_ts.heading(c, text=heads[c])
            self.tree_ts.column(c, width=widths[c], anchor="center" if c in ("id", "mhp", "mhd", "mht") else "w")
        vsb.pack(side="right", fill="y")
        hsb.pack(side="bottom", fill="x")
        self.tree_ts.pack(fill="both", expand=True)
        self.tree_ts.bind("<Double-Button-1>", lambda _e: self.ts_affecter())
        self.tree_ts.tag_configure("affecte", foreground="#0e7c66")
        self.tree_ts.tag_configure("libre", foreground="#b03030")

        self.load_tableau_service()

    # ---------------- DONNEES ----------------
    def ts_formateurs_list(self):
        """Formateurs proposés pour l'affectation : formateurs du Personnel (pas les administrateurs) + Vacataires."""
        out = []
        with get_db_connection() as conn:
            for (n, p) in conn.execute("SELECT nom, prenom FROM personnel WHERE fonction LIKE '%formateur%' ORDER BY nom"):
                out.append(f"{(n or '').upper()} {p or ''}".strip())
            for (n, p) in conn.execute("SELECT nom, prenom FROM vacataires ORDER BY nom"):
                nom = f"{(n or '')} {p or ''}".strip()
                if nom and nom not in out:
                    out.append(nom)
        return out

    def load_tableau_service(self):
        if not hasattr(self, "tree_ts"):
            return
        for i in self.tree_ts.get_children():
            self.tree_ts.delete(i)
        with get_db_connection() as conn:
            rows = conn.execute("SELECT id, groupe, filiere, creneau, module, mhp_totale, mhd_totale, mht, affectation "
                                "FROM tableau_service").fetchall()
        q = self.ts_search.get().strip().casefold()
        ff = self.ts_filt_filiere.get()
        fg = self.ts_filt_groupe.get()
        only_free = bool(self.ts_only_free.get())
        # listes de filtres (sans ecraser la selection courante)
        fils = sorted({(r[2] or "—") for r in rows})
        grps = sorted({(r[1] or "—") for r in rows})
        self.ts_filt_filiere.configure(values=["Toutes les filières"] + fils)
        self.ts_filt_groupe.configure(values=["Tous les groupes"] + grps)

        n_aff, tot_mhp, tot_mhd, tot_mht, aff_set = 0, 0.0, 0.0, 0.0, set()

        def _f(v):
            try:
                return float(str(v).replace(",", "."))
            except (TypeError, ValueError):
                return 0.0

        for r in rows:
            rid, groupe, filiere, creneau, module, mhp, mhd, mht, affectation = r
            if q and q not in " ".join(str(x or "") for x in r[1:]).casefold():
                continue
            if ff and ff != "Toutes les filières" and (filiere or "—") != ff:
                continue
            if fg and fg != "Tous les groupes" and (groupe or "—") != fg:
                continue
            if only_free and affectation:
                continue
            tag = "affecte" if affectation else "libre"
            self.tree_ts.insert("", "end", iid=str(rid), tags=(tag,), values=(
                rid, groupe or "—", filiere or "—", creneau or "—", module or "—",
                mhp or "—", mhd or "—", mht or "—", affectation or "—"))
            if affectation:
                n_aff += 1
                aff_set.add(affectation)
            tot_mhp += _f(mhp); tot_mhd += _f(mhd); tot_mht += _f(mht)
        total = len(rows)
        pct = (n_aff * 100 // total) if total else 0
        self.lbl_ts_stats.configure(text=f"{total} module(s)  ·  MHP {tot_mhp:.1f} h  ·  MHD {tot_mhd:.1f} h  ·  "
                                         f"MHT {tot_mht:.1f} h  ·  {n_aff} affecté(s) ({pct} %)  ·  "
                                         f"{len(aff_set)} formateur(s)")
        self.combo_ts_aff.configure(values=self.ts_formateurs_list() or ["—"])

    # ---------------- AFFECTATION ----------------
    def ts_affecter(self):
        sel = self.tree_ts.selection()
        if not sel:
            messagebox.showinfo("Affectation", "Sélectionnez au moins un module dans le tableau.")
            return
        nom = self.combo_ts_aff.get().strip()
        if not nom or nom == "—":
            messagebox.showerror("Erreur", "Choisissez un formateur dans la liste déroulante.")
            return
        with get_db_connection() as conn:
            for iid in sel:
                conn.execute("UPDATE tableau_service SET affectation=? WHERE id=?", (nom, int(iid)))
            conn.commit()
        self.load_tableau_service()

    def ts_desaffecter(self):
        sel = self.tree_ts.selection()
        if not sel:
            messagebox.showinfo("Affectation", "Sélectionnez au moins un module dans le tableau.")
            return
        with get_db_connection() as conn:
            for iid in sel:
                conn.execute("UPDATE tableau_service SET affectation=NULL WHERE id=?", (int(iid),))
            conn.commit()
        self.load_tableau_service()

    # ---------------- IMPORT / EXPORT EXCEL ----------------
    @staticmethod
    def _name_key(s):
        """Cle de comparaison d'un nom : ensemble de mots sans accents (ordre nom/prenom indifferent)."""
        s = unicodedata.normalize("NFKD", str(s or "")).encode("ascii", "ignore").decode().casefold()
        return frozenset(re.findall(r"[a-z0-9]+", s))

    def _ts_read_sheet(self, path):
        """Lit la feuille « TDS ISTA AHFIR » (a defaut, la premiere feuille qui contient les colonnes
        Module et Groupe). La ligne d'en-tete est detectee automatiquement.
        Retourne (nom_de_la_feuille, [ {colonne_base: texte} ])."""
        xl = pd.ExcelFile(path)
        norm = self._ts_norm
        sheets = list(xl.sheet_names)
        ordre = [s for s in sheets if norm(s) == "tds ista ahfir"]
        ordre += [s for s in sheets if s not in ordre and "ahfir" in norm(s)]
        ordre += [s for s in sheets if s not in ordre]
        table = {}
        for norm_h, db, _disp in self.TS_COLS:
            table.setdefault(norm_h, db)

        def clean(v):
            if v is None or (not isinstance(v, str) and pd.isna(v)):
                return ""
            t = re.sub(r"\s+", " ", str(v)).strip()
            if t.lower() == "nan":
                return ""
            return re.sub(r"^(-?\d+)\.0+$", r"\1", t)

        for sh in ordre:
            head = xl.parse(sh, header=None, dtype=str, nrows=40)
            hdr = None
            for k in range(len(head)):
                cells = {norm(v) for v in head.iloc[k].tolist() if isinstance(v, str)}
                if "module" in cells and "groupe" in cells:
                    hdr = k
                    break
            if hdr is None:
                continue
            raw = xl.parse(sh, header=None, dtype=str)
            idx = {}
            for c, v in enumerate(raw.iloc[hdr].tolist()):
                db = table.get(norm(v)) if isinstance(v, str) else None
                if db and db not in idx:
                    idx[db] = c
            if "module" not in idx or "groupe" not in idx:
                continue
            lignes = []
            for r in raw.iloc[hdr + 1:].itertuples(index=False):
                vals = {db: clean(r[c]) for db, c in idx.items()}
                if vals.get("module"):
                    lignes.append(vals)
            return sh, lignes
        return None, []

    def import_tableau_service(self):
        path = filedialog.askopenfilename(title="Importer le tableau de service (Excel DRIF)",
                                          filetypes=[("Fichiers Excel", "*.xlsx *.xlsm *.xls")])
        if not path:
            return
        try:
            feuille, lignes = self._ts_read_sheet(path)
        except Exception as e:
            messagebox.showerror("Erreur", f"Impossible de lire le fichier :\n{e}")
            return
        if not lignes:
            messagebox.showerror("Erreur",
                                 "Aucune feuille ne contient les colonnes obligatoires (« Module » et « Groupe »).\n"
                                 "Le fichier doit contenir la feuille « TDS ISTA AHFIR » (modèle DRIF).")
            return
        if not messagebox.askyesno("Importer",
                                   f"Feuille « {feuille} » : {len(lignes)} module(s) trouvé(s).\n\n"
                                   "L'import REMPLACERA les données actuelles du tableau de service.\n"
                                   "Les formateurs de la colonne « Nom & Prénom du Formateur » seront affectés automatiquement.\n\n"
                                   "Continuer ?"):
            return
        # formateurs deja connus (Personnel + Vacataires) : on reprend leur ecriture pour rester coherent
        connus = {}
        with get_db_connection() as conn:
            for (n, p) in conn.execute("SELECT nom, prenom FROM personnel WHERE fonction LIKE '%formateur%'"):
                connus.setdefault(self._name_key(f"{n} {p}"), f"{(n or '').upper()} {p or ''}".strip())
            for (n, p) in conn.execute("SELECT nom, prenom FROM vacataires"):
                connus.setdefault(self._name_key(f"{n} {p}"), f"{n or ''} {p or ''}".strip())
        db_cols = [c for c in self.TS_DB_COLS if c != "affectation"]
        vals, inconnus, formateurs = [], [], set()
        for v in lignes:
            f = v.get("formateur", "")
            aff = None
            if f:
                k = self._name_key(f)
                aff = connus.get(k, f)
                formateurs.add(aff)
                if k not in connus and f not in inconnus:
                    inconnus.append(f)
            vals.append(tuple(v.get(c, "") for c in db_cols) + (aff,))
        with get_db_connection() as conn:
            conn.execute("DELETE FROM tableau_service")
            conn.executemany(f"INSERT INTO tableau_service ({', '.join(db_cols + ['affectation'])}) "
                             f"VALUES ({', '.join('?' * (len(db_cols) + 1))})", vals)
            conn.commit()
        n_aff = sum(1 for r in vals if r[-1])
        msg = (f"✅  {len(vals)} module(s) importé(s) depuis « {feuille} ».\n\n"
               f"• {n_aff} module(s) affecté(s) à {len(formateurs)} formateur(s)\n"
               f"• {len(vals) - n_aff} module(s) sans formateur")
        if inconnus:
            msg += ("\n\n⚠  Formateurs absents de la liste Personnel / Vacataires :\n   " + "\n   ".join(inconnus[:15]) +
                    ("\n   ..." if len(inconnus) > 15 else "") +
                    "\n(Ajoutez-les dans Formateurs pour renseigner leur masse statutaire.)")
        messagebox.showinfo("Succès", msg)
        self.load_tableau_service()

    def export_tableau_service(self):
        with get_db_connection() as conn:
            cur = conn.execute("SELECT * FROM tableau_service")
            cols = [d[0] for d in cur.description]
            rows = cur.fetchall()
        if not rows:
            messagebox.showinfo("Export", "Aucune donnée à exporter.")
            return
        seen = {}
        for _norm, db, disp in self.TS_COLS:
            if db not in seen:
                seen[db] = disp
        headers = [seen.get(c, "Affectation" if c == "affectation" else c) for c in cols]
        chemin = filedialog.asksaveasfilename(title="Exporter le tableau de service",
                                              defaultextension=".xlsx",
                                              filetypes=[("Fichier Excel", "*.xlsx")],
                                              initialfile="Tableau_de_service.xlsx")
        if not chemin:
            return
        try:
            df = pd.DataFrame(rows, columns=headers)
            with pd.ExcelWriter(chemin, engine="openpyxl") as writer:
                df.to_excel(writer, index=False, sheet_name="Tableau de service")
            messagebox.showinfo("Export réussi", f"✅  Fichier exporté avec succès :\n{chemin}")
        except Exception as e:
            messagebox.showerror("Erreur d'exportation", f"Impossible d'exporter :\n{e}")

    # ---------------- TDS : SYNTHESE PAR FORMATEUR ----------------
    @staticmethod
    def _tdf(v):
        try:
            return float(str(v).replace(",", "."))
        except (TypeError, ValueError):
            return 0.0

    @staticmethod
    def _grp_sort(g):
        return (0, int(g), g) if str(g).isdigit() else (1, 0, str(g))

    def _tds_data(self):
        """{formateur: {mods, groupes, mhp, mhd, mht, s1, s2}} d'apres les modules affectes."""
        with get_db_connection() as conn:
            rows = conn.execute("SELECT affectation, groupe, filiere, module, code_module, mhp_totale, mhd_totale, "
                                "mht, mht_s1, mht_s2 FROM tableau_service "
                                "WHERE affectation IS NOT NULL AND TRIM(affectation) != '' "
                                "ORDER BY affectation, filiere, groupe, module").fetchall()
        data = {}
        for aff, groupe, filiere, module, code, mhp, mhd, mht, s1, s2 in rows:
            d = data.setdefault(aff, {"mods": [], "groupes": set(), "mhp": 0.0, "mhd": 0.0,
                                      "mht": 0.0, "s1": 0.0, "s2": 0.0})
            d["mods"].append((module or "—", code or "", groupe or "—", filiere or "—", self._tdf(mhp),
                              self._tdf(mhd), self._tdf(mht), self._tdf(s1), self._tdf(s2)))
            if groupe:
                d["groupes"].add(groupe)
            d["mhp"] += self._tdf(mhp); d["mhd"] += self._tdf(mhd); d["mht"] += self._tdf(mht)
            d["s1"] += self._tdf(s1); d["s2"] += self._tdf(s2)
        return data

    def show_tds(self):
        """TDS : pour chaque formateur, les groupes, la masse horaire a travailler (MHP/MHD/MHT, S1, S2)
        et la liste detaillee des modules affectes."""
        data = self._tds_data()
        if not data:
            messagebox.showinfo("TDS", "Aucun module affecté pour le moment.\n\n"
                                       "Importez le fichier Excel (feuille « TDS ISTA AHFIR ») ou affectez les modules à la main.")
            return

        win = ctk.CTkToplevel(self)
        win.title("TDS — Tableau de service par formateur")
        win.geometry("1180x640")
        win.grab_set()

        topw = ctk.CTkFrame(win, fg_color="transparent")
        topw.pack(fill="x", padx=15, pady=(12, 6))
        ctk.CTkLabel(topw, text="📋  TDS — Masse horaire à travailler et groupes de chaque formateur",
                     font=ctk.CTkFont(size=17, weight="bold")).pack(side="left")
        ctk.CTkButton(topw, text="📤  Exporter Excel", fg_color="#217346", hover_color="#145a30",
                      command=self.export_tds).pack(side="right")

        wrap = ctk.CTkFrame(win)
        wrap.pack(fill="both", expand=True, padx=15, pady=6)
        cols = ("formateur", "groupes", "nmod", "mhp", "mhd", "s1", "s2", "mht")
        tree = ttk.Treeview(wrap, columns=cols, show="tree headings", selectmode="browse", height=22)
        tree.heading("#0", text="Modules (module · groupe · filière · MHT S1 / S2 / total)")
        tree.column("#0", width=430, anchor="w")
        for c, h, w in (("formateur", "Formateur", 200), ("groupes", "Groupes", 130), ("nmod", "Modules", 65),
                        ("mhp", "MHP", 70), ("mhd", "MHD", 70), ("s1", "MHT S1", 75), ("s2", "MHT S2", 75),
                        ("mht", "Masse à travailler (MHT)", 150)):
            tree.heading(c, text=h)
            tree.column(c, width=w, anchor="w" if c in ("formateur", "groupes") else "center")
        vsb = ttk.Scrollbar(wrap, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        tree.pack(fill="both", expand=True)

        for i, (aff, d) in enumerate(sorted(data.items(), key=lambda kv: kv[0].casefold())):
            pid = f"TDS{i}"
            grp = ", ".join(sorted(d["groupes"], key=self._grp_sort)) or "—"
            tree.insert("", "end", iid=pid, open=False, tags=("parent",), values=(
                aff, grp, len(d["mods"]), "%g" % d["mhp"], "%g" % d["mhd"], "%g" % d["s1"], "%g" % d["s2"], "%g h" % d["mht"]))
            for module, code, groupe, filiere, mhp, mhd, mht, s1, s2 in d["mods"]:
                tree.insert(pid, "end", values=("", "", "", "", "", "", "", ""),
                            text=f"{module}   ·   {groupe}   ·   {filiere}   ·   {s1:g} / {s2:g} / {mht:g}")
        tree.tag_configure("parent", foreground="#0d2c54")
        tot = {k: sum(d[k] for d in data.values()) for k in ("mht", "s1", "s2")}
        ctk.CTkLabel(win, text=f"{len(data)} formateur(s)  ·  masse totale affectée : {tot['mht']:g} h  "
                               f"(S1 : {tot['s1']:g} h  ·  S2 : {tot['s2']:g} h)  ·  Cliquez sur ▸ pour voir le détail des modules.",
                     font=ctk.CTkFont(size=12, weight="bold"), text_color="#6b7a89").pack(anchor="w", padx=18, pady=(0, 10))

    def export_tds(self):
        """Exporte le TDS en Excel : synthese + detail + UNE FEUILLE PAR FORMATEUR (son tableau de service)."""
        data = self._tds_data()
        if not data:
            messagebox.showinfo("Export TDS", "Aucun module affecté à exporter.")
            return
        chemin = filedialog.asksaveasfilename(title="Exporter le TDS", defaultextension=".xlsx",
                                              filetypes=[("Fichier Excel", "*.xlsx")],
                                              initialfile="TDS_Formateurs.xlsx")
        if not chemin:
            return
        try:
            resume, detail = [], []
            ordre = sorted(data.items(), key=lambda kv: kv[0].casefold())
            for aff, d in ordre:
                resume.append([aff, ", ".join(sorted(d["groupes"], key=self._grp_sort)), len(d["mods"]),
                               round(d["mhp"], 2), round(d["mhd"], 2), round(d["s1"], 2), round(d["s2"], 2), round(d["mht"], 2)])
                for module, code, groupe, filiere, mhp, mhd, mht, s1, s2 in d["mods"]:
                    detail.append([aff, filiere, groupe, code, module, mhp, mhd, s1, s2, mht])
            c_det = ["Formateur", "Filière", "Groupe", "Code module", "Module", "MHP", "MHD", "MHT S1", "MHT S2", "MHT"]
            with pd.ExcelWriter(chemin, engine="openpyxl") as writer:
                pd.DataFrame(resume, columns=["Formateur", "Groupes", "Nombre de modules", "MHP total", "MHD total",
                                              "MHT S1", "MHT S2", "Masse à travailler (MHT)"]
                             ).to_excel(writer, index=False, sheet_name="Synthèse")
                pd.DataFrame(detail, columns=c_det).to_excel(writer, index=False, sheet_name="Détail modules")
                pris = {"Synthèse", "Détail modules"}
                for aff, d in ordre:
                    nom = re.sub(r"[\\/*?:\[\]]", " ", aff).strip()[:28] or "Formateur"
                    base, k = nom, 2
                    while nom in pris:
                        nom = f"{base[:25]}_{k}"; k += 1
                    pris.add(nom)
                    rows = [[f, g, c, m, p, dd, s1, s2, t] for (m, c, g, f, p, dd, t, s1, s2) in d["mods"]]
                    rows.append(["TOTAL", ", ".join(sorted(d["groupes"], key=self._grp_sort)), "", "",
                                 round(d["mhp"], 2), round(d["mhd"], 2), round(d["s1"], 2), round(d["s2"], 2), round(d["mht"], 2)])
                    pd.DataFrame(rows, columns=["Filière", "Groupe", "Code module", "Module", "MHP", "MHD",
                                                "MHT S1", "MHT S2", "MHT"]).to_excel(writer, index=False, sheet_name=nom)
            messagebox.showinfo("Export réussi", f"✅  Fichier exporté avec succès :\n{chemin}\n\n"
                                                 "Il contient la synthèse, le détail et une feuille par formateur.")
        except Exception as e:
            messagebox.showerror("Erreur d'exportation", f"Impossible d'exporter :\n{e}")

    # ---------------- TDS OFFICIEL (style OFPPT, comme le modele image) ----------------
    def generer_tds_officiel(self):
        """Genere le TABLEAU DE SERVICE officiel en PDF (paysage A4), une page
        par formateur : logo OFPPT, titre, annee de formation, complexe, nom du
        formateur, tableau Filiere/Groupe/Code Module/Module/EFM/MHP-MHSYN-MHT
        S1-S2 + MHT, ligne Total general par formateur, et une page finale
        RECAPITULATIF GENERAL avec le total de tous les formateurs."""
        import textwrap

        with get_db_connection() as conn:
            rows = conn.execute(
                "SELECT affectation, exercice, filiere, groupe, code_module, module, efm_regional, "
                "mhp_s1, mhsyn_s1, mht_s1, mhp_s2, mhsyn_s2, mht_s2, mht "
                "FROM tableau_service WHERE affectation IS NOT NULL AND TRIM(affectation) != '' "
                "ORDER BY affectation, filiere, groupe, module").fetchall()
        if not rows:
            messagebox.showinfo("TDS", "Aucun module affecté pour le moment.\n\n"
                                       "Sélectionnez des modules dans le tableau, choisissez un formateur "
                                       "puis cliquez « Affecter ».")
            return

        def _num(v):
            try:
                return float(str(v).replace(",", "."))
            except (TypeError, ValueError):
                return 0.0

        def _fmt(v):
            try:
                f = float(str(v).replace(",", "."))
                s = "%g" % f
                return s.replace(".", ",") if "." in s else s
            except (TypeError, ValueError):
                return str(v or "")

        data, exercice = {}, ""
        for r in rows:
            if not exercice and r[1]:
                exercice = str(r[1]).strip()
            data.setdefault(r[0], []).append(r[2:])
        if not exercice:
            y = datetime.now().year
            exercice = f"{y}/{y + 1}"

        COLS = [("Filière", 50, "L"), ("Groupe", 11, "C"), ("Code\nModule", 16, "C"),
                ("Module", 60, "L"), ("EFM\nRégional", 11, "C"),
                ("Somme de\nMHP S1", 18, "C"), ("Somme de\nMHSYN S1", 18, "C"),
                ("Somme de\nMHT S1", 18, "C"), ("Somme de\nMHP S2", 18, "C"),
                ("Somme de\nMHSYN S2", 18, "C"), ("Somme de\nMHT S2", 18, "C"),
                ("Somme de\nMHT", 18, "C")]

        pdf = FPDF(orientation="L", unit="mm", format="A4")
        pdf.set_margins(10, 10, 10)
        pdf.set_auto_page_break(False)

        def draw_logo():
            """Logo OFPPT centre en haut de page (remplace le texte de l'office)."""
            logo_png = os.path.join(BASE_DIR, "logo_ofppt.png")
            logo_jpg = os.path.join(BASE_DIR, "logo_ofppt.jpg")
            wlogo = 48
            xlogo = (pdf.w - wlogo) / 2
            try:
                if os.path.exists(logo_png):
                    pdf.image(logo_png, x=xlogo, y=9, w=wlogo)
                    return True
                if os.path.exists(logo_jpg):
                    pdf.image(logo_jpg, x=xlogo, y=9, w=wlogo)
                    return True
            except Exception:
                logger.warning("Logo illisible pour le TDS", exc_info=True)
            # repli : texte institutionnel centre si aucun logo n'est disponible
            pdf.set_text_color(0, 0, 0)
            pdf.set_font("Arial", "B", 11)
            pdf.set_xy(10, 13)
            pdf.cell(pdf.w - 20, 6, clean_str("Office de la Formation Professionnelle et de la Promotion du Travail"), align="C")
            pdf.set_font("Arial", "I", 9)
            pdf.set_xy(10, 20)
            pdf.cell(pdf.w - 20, 5, clean_str("Complexe de Formation Professionnelle de Berkane - ISTA Ahfir"), align="C")
            return False

        def draw_page_header(aff):
            pdf.add_page()
            draw_logo()
            pdf.set_text_color(0, 0, 0)
            pdf.set_font("Arial", "B", 15)
            pdf.set_xy(10, 40)
            pdf.cell(277, 8, clean_str("TABLEAU DE SERVICE"), align="C", ln=1)
            pdf.set_font("Arial", "B", 11)
            pdf.cell(277, 6, clean_str(f"Année de formation : {exercice}"), align="C", ln=1)
            pdf.ln(3)
            pdf.set_fill_color(31, 83, 141)
            pdf.set_text_color(255, 255, 255)
            pdf.set_font("Arial", "B", 10)
            pdf.cell(62, 7, clean_str(self.TS_COMPLEXE), align="C", fill=True, ln=1)
            pdf.set_text_color(0, 0, 0)
            pdf.set_font("Arial", "B", 9)
            pdf.set_fill_color(220, 230, 241)
            pdf.cell(62, 6, clean_str("Nom & Prénom du Formateur"), align="C", fill=True)
            pdf.set_font("Arial", "B", 10)
            pdf.cell(0, 6, clean_str("    " + aff), ln=1)
            pdf.ln(2)

        def draw_table_header():
            h = 11
            y0 = pdf.get_y()
            x0 = pdf.l_margin
            pdf.set_fill_color(217, 225, 242)
            pdf.set_font("Arial", "B", 8)
            for label, w, _a in COLS:
                pdf.rect(x0, y0, w, h, style="F")
                pdf.rect(x0, y0, w, h)
                lignes = label.split("\n")
                lh = h / len(lignes)
                for i, ln in enumerate(lignes):
                    pdf.set_xy(x0, y0 + i * lh)
                    pdf.cell(w, lh, clean_str(ln), align="C")
                x0 += w
            pdf.set_xy(pdf.l_margin, y0 + h)

        def draw_row(vals, h, bold=False, fill=None):
            y0 = pdf.get_y()
            x0 = pdf.l_margin
            if fill:
                pdf.set_fill_color(*fill)
            for (label, w, align), v in zip(COLS, vals):
                pdf.rect(x0, y0, w, h, style="F" if fill else "D")
                pdf.set_font("Arial", "B" if bold else "", 7.5)
                s = str(v if v is not None else "")
                lignes = s.split("\n")
                lh = h / len(lignes)
                for i, ln in enumerate(lignes):
                    pdf.set_xy(x0, y0 + i * lh)
                    pdf.cell(w, lh, clean_str(ln), align=align)
                x0 += w
            pdf.set_xy(pdf.l_margin, y0 + h)

        # ---------- une page par formateur ----------
        recap = []  # (formateur, nb modules, mhp1, mhsyn1, mht1, mhp2, mhsyn2, mht2, mht)
        for aff, items in sorted(data.items(), key=lambda kv: kv[0].casefold()):
            draw_page_header(aff)
            draw_table_header()
            tot = [0.0] * 7
            for it in items:
                nums = [_num(x) for x in it[5:12]]
                for k in range(7):
                    tot[k] += nums[k]
                ftxt = "\n".join(textwrap.wrap(str(it[0] or ""), 30)) or "—"
                mtxt = "\n".join(textwrap.wrap(str(it[3] or ""), 36)) or "—"
                vals = [ftxt, str(it[1] or ""), str(it[2] or ""), mtxt, str(it[4] or "")]
                vals += [_fmt(x) for x in it[5:12]]
                nlines = max(ftxt.count("\n"), mtxt.count("\n")) + 1
                h = 5.6 * nlines
                if pdf.get_y() + h > 188:
                    pdf.add_page()
                    draw_table_header()
                draw_row(vals, h)
            if pdf.get_y() + 7 > 188:
                pdf.add_page()
                draw_table_header()
            draw_row(["Total général", "", "", "", ""] + [_fmt(x) for x in tot],
                     7, bold=True, fill=(242, 242, 242))
            recap.append([aff, len(items)] + tot)

        # ---------- page finale : RECAPITULATIF GENERAL (total a la fin) ----------
        pdf.add_page()
        draw_logo()
        pdf.set_text_color(0, 0, 0)
        pdf.set_font("Arial", "B", 15)
        pdf.set_xy(10, 40)
        pdf.cell(277, 8, clean_str("RÉCAPITULATIF GÉNÉRAL - TABLEAU DE SERVICE"), align="C", ln=1)
        pdf.set_font("Arial", "B", 11)
        pdf.cell(277, 6, clean_str(f"Année de formation : {exercice}"), align="C", ln=1)
        pdf.ln(4)

        RCOLS = [("Formateur", 92, "L"), ("Modules", 18, "C"),
                 ("MHP S1", 23, "C"), ("MHSYN S1", 23, "C"), ("MHT S1", 23, "C"),
                 ("MHP S2", 23, "C"), ("MHSYN S2", 23, "C"), ("MHT S2", 23, "C"),
                 ("MHT", 23, "C")]

        def rc_draw_header():
            h = 8
            y0 = pdf.get_y()
            x0 = pdf.l_margin
            pdf.set_fill_color(31, 83, 141)
            pdf.set_text_color(255, 255, 255)
            pdf.set_font("Arial", "B", 9)
            for label, w, _a in RCOLS:
                pdf.rect(x0, y0, w, h, style="F")
                pdf.set_xy(x0, y0)
                pdf.cell(w, h, clean_str(label), align="C")
                x0 += w
            pdf.set_text_color(0, 0, 0)
            pdf.set_xy(pdf.l_margin, y0 + h)

        def rc_draw(vals, bold=False, fill=None):
            h = 7
            y0 = pdf.get_y()
            x0 = pdf.l_margin
            if fill:
                pdf.set_fill_color(*fill)
            for (label, w, align), v in zip(RCOLS, vals):
                pdf.rect(x0, y0, w, h, style="F" if fill else "D")
                pdf.set_font("Arial", "B" if bold else "", 9)
                pdf.set_xy(x0, y0)
                pdf.cell(w, h, clean_str(str(v)), align=align)
                x0 += w
            pdf.set_xy(pdf.l_margin, y0 + h)

        rc_draw_header()
        gtot = [0.0] * 7
        for ligne in recap:
            rc_draw([ligne[0], ligne[1]] + [_fmt(x) for x in ligne[2:]])
            for k in range(7):
                gtot[k] += ligne[2 + k]
        rc_draw(["TOTAL GÉNÉRAL", sum(x[1] for x in recap)] + [_fmt(x) for x in gtot],
                bold=True, fill=(217, 225, 242))

        self.open_pdf_viewer(pdf, f"TDS_Tableau_de_service_{exercice.replace('/', '-')}.pdf",
                             "Tableau de service (TDS)")

    # --- PAGE D'ACCUEIL ---
    def show_accueil(self):
        """Page d'accueil simple et professionnelle : en-tete sobre, statistiques
        du jour et acces direct aux modules."""
        self.clear_main_frame()
        self.set_active_nav("accueil")

        # ---------------- donnees ----------------
        with get_db_connection() as conn:
            cursor = conn.cursor()

            def count(sql, *args):
                try:
                    cursor.execute(sql, args)
                    return cursor.fetchone()[0]
                except Exception:
                    return 0

            nb_personnel = count("SELECT COUNT(*) FROM personnel")
            nb_formateurs = count("SELECT COUNT(*) FROM personnel WHERE fonction LIKE '%formateur%'")
            nb_vacataires = count("SELECT COUNT(*) FROM vacataires")
            nb_formations = count("SELECT COUNT(*) FROM formations")
            nb_absences = count("SELECT COUNT(*) FROM absences")
            nb_om = count("SELECT COUNT(*) FROM ordres_mission")

            today = datetime.now().strftime("%d/%m/%Y")
            absents_auj = count(
                "SELECT COUNT(*) FROM absences WHERE date_debut <= ? AND date_fin >= ?", today, today)
            formations_15j = 0
            try:
                cursor.execute("SELECT date_debut FROM formations")
                d0 = datetime.now().date()
                for (d1,) in cursor.fetchall():
                    try:
                        delta = (datetime.strptime(d1, "%d/%m/%Y").date() - d0).days
                        if 0 <= delta <= 15:
                            formations_15j += 1
                    except Exception:
                        logger.debug("Date de formation invalide : %r", d1)
            except Exception:
                logger.exception("Calcul des formations a venir impossible")

        # ---------------- style ----------------
        PRIMARY = PALETTE["primary"]
        DARK = PALETTE["navy"]
        TXT = ("#1c2b3a", "#e8edf2")
        MUTED = ("#64748b", "#9aa7b4")
        CARD = ("#ffffff", "#23272e")
        BORDER = ("#dfe6ee", "#3a3f46")
        BG = ("#f4f6f9", "#1b1e24")

        def font(size, bold=False):
            return ctk.CTkFont(size=size, weight="bold" if bold else "normal")

        # ================= EN-TETE =================
        header = ctk.CTkFrame(self.main_frame, fg_color=DARK, corner_radius=0, height=84)
        header.pack(fill="x")
        header.pack_propagate(False)

        left = ctk.CTkFrame(header, fg_color="transparent")
        left.pack(side="left", padx=24, pady=14)
        self._home_logo_img = None
        try:
            from PIL import Image
            src = next((p for p in (os.path.join(BASE_DIR, "logo_ofppt.png"),
                                    os.path.join(BASE_DIR, "logo_ofppt.jpg")) if os.path.exists(p)), None)
            if src:
                img = Image.open(src).convert("RGBA")
                w, h = img.size
                self._home_logo_img = ctk.CTkImage(light_image=img, dark_image=img,
                                                   size=(max(1, int(w * 44 / h)), 44))
        except Exception:
            self._home_logo_img = None
        if self._home_logo_img:
            ctk.CTkLabel(left, image=self._home_logo_img, text="").pack(side="left", padx=(0, 14))
        else:
            ctk.CTkLabel(left, text="OFPPT", font=font(18, True), text_color=PALETTE["accent"]).pack(side="left", padx=(0, 14))
        ttl = ctk.CTkFrame(left, fg_color="transparent")
        ttl.pack(side="left")
        ctk.CTkLabel(ttl, text="Tableau de bord", font=font(22, True), text_color="white").pack(anchor="w")
        ctk.CTkLabel(ttl, text="Complexe de Formation Professionnelle — Berkane",
                     font=font(12), text_color="#9db8d9").pack(anchor="w")

        right = ctk.CTkFrame(header, fg_color="transparent")
        right.pack(side="right", padx=24, pady=14)
        jours = ["Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi", "Samedi", "Dimanche"]
        mois = ["janvier", "février", "mars", "avril", "mai", "juin", "juillet",
                "août", "septembre", "octobre", "novembre", "décembre"]
        now = datetime.now()
        ctk.CTkLabel(right, text=f"{jours[now.weekday()]} {now.day} {mois[now.month - 1]} {now.year}",
                     font=font(15, True), text_color="white").pack(anchor="e")
        ctk.CTkLabel(right, text=f"{nb_personnel} agents  ·  {nb_formateurs} formateurs  ·  {nb_vacataires} vacataires",
                     font=font(11), text_color="#9db8d9").pack(anchor="e")

        # barre doree fine sous l'en-tete
        ctk.CTkFrame(self.main_frame, fg_color=PALETTE["accent"], height=3, corner_radius=0).pack(fill="x")

        # ---------------- zone scrollable ----------------
        scroll = ctk.CTkScrollableFrame(self.main_frame, fg_color=BG)
        scroll.pack(fill="both", expand=True, padx=0, pady=0)

        # ================= BANDEAU INFOS DU JOUR =================
        info = ctk.CTkFrame(scroll, fg_color="transparent")
        info.pack(fill="x", padx=24, pady=(16, 4))

        def info_chip(parent, texte, couleur, commande):
            c = ctk.CTkButton(parent, text=texte, font=font(12, True), height=34,
                              corner_radius=10, fg_color=couleur, hover_color=PALETTE["primary_dark"],
                              text_color="white", command=commande)
            c.pack(side="left", padx=(0, 10))
            return c

        info_chip(info, f"🩺  {absents_auj} absent(s) aujourd'hui", "#c0392b",
                  lambda: AbsencesListWindow(self))
        info_chip(info, f"📚  {formations_15j} formation(s) à venir (15 j)", PALETTE["primary"],
                  lambda: FormationsListWindow(self))
        info_chip(info, f"✈️  {nb_om} ordre(s) de mission", "#1b8a5a",
                  self.show_ordre_mission_module)

        # ================= STATISTIQUES =================
        stats = ctk.CTkFrame(scroll, fg_color="transparent")
        stats.pack(fill="x", padx=24, pady=(10, 0))
        for i in range(5):
            stats.grid_columnconfigure(i, weight=1, uniform="stat")

        def stat_card(col, valeur, label, couleur, commande):
            card = ctk.CTkFrame(stats, corner_radius=10, border_width=1, border_color=BORDER,
                                fg_color=CARD, cursor="hand2", height=64)
            card.grid(row=0, column=col, sticky="nsew", padx=5, pady=2)
            card.pack_propagate(False)
            ctk.CTkFrame(card, width=4, corner_radius=2, fg_color=couleur).pack(
                side="left", fill="y", padx=(10, 0), pady=8)
            body = ctk.CTkFrame(card, fg_color="transparent")
            body.pack(side="left", fill="both", expand=True, padx=10, pady=4)
            lig = ctk.CTkFrame(body, fg_color="transparent")
            lig.pack(expand=True)
            ctk.CTkLabel(lig, text=str(valeur), font=font(20, True), text_color=couleur).pack(side="left", padx=(0, 8))
            ctk.CTkLabel(lig, text=label, font=font(12), text_color=MUTED).pack(side="left")
            for w in (card, body, lig):
                w.bind("<Button-1>", lambda _e: commande())

        stat_card(0, nb_personnel, "Personnel", PALETTE["primary"], self.show_personnel)
        stat_card(1, nb_formateurs, "Formateurs", "#0e7c66", self.show_formateurs)
        stat_card(2, nb_vacataires, "Vacataires", "#6a4fb3", self.show_vacataires)
        stat_card(3, nb_absences, "Absences", "#d98219", lambda: AbsencesListWindow(self))
        stat_card(4, nb_om, "Ordres de mission", "#1b8a5a", self.show_ordre_mission_module)

        # ================= MODULES =================
        ctk.CTkLabel(scroll, text="MODULES", font=font(14, True), text_color=TXT).pack(
            anchor="w", padx=29, pady=(18, 2))
        ctk.CTkLabel(scroll, text="Accédez directement aux rubriques de la gestion",
                     font=font(11), text_color=MUTED).pack(anchor="w", padx=29)

        grid = ctk.CTkFrame(scroll, fg_color="transparent")
        grid.pack(fill="x", padx=24, pady=(6, 4))
        for i in range(4):
            grid.grid_columnconfigure(i, weight=1, uniform="mod")

        modules = [
            ("👥", "Personnel", "Agents, administrateurs et formateurs", self.show_personnel),
            ("👨‍🏫", "Formateurs", "Permanents et vacataires", self.show_formateurs),
            ("📅", "Emploi du temps", "Grilles, salles, groupes, séances", lambda: self.show_emploi_module("directeur")),
            ("📊", "Analyse", "Masse horaire des formateurs", self.show_analysis),
            ("🗂️", "Tableau de service", "Affectation des modules (DRIF)", self.show_tableau_service),
            ("📋", "Suivi d'absence", "Absences et congés", self.show_suivi_absence),
            ("📚", "Formations", "Planification des sessions", self.show_formation),
            ("✈️", "Ordre de mission", "Missions et déplacements", self.show_ordre_mission_module),
            ("🎓", "Vacataires", "Intervenants externes", self.show_vacataires),
            ("⚙️", "Paramètres", "Comptes, thème et données", lambda: SettingsWindow(self, self.logout)),
        ]
        for i, (icone, titre, desc, cmd) in enumerate(modules):
            card = ctk.CTkFrame(grid, corner_radius=12, border_width=1, border_color=BORDER,
                                fg_color=CARD, cursor="hand2")
            card.grid(row=i // 4, column=i % 4, sticky="nsew", padx=5, pady=6)
            ent = ctk.CTkFrame(card, fg_color="transparent")
            ent.pack(fill="both", expand=True, padx=16, pady=14)
            ctk.CTkLabel(ent, text=icone, font=ctk.CTkFont(size=26)).pack(anchor="w")
            ctk.CTkLabel(ent, text=titre, font=font(15, True), text_color=TXT).pack(anchor="w", pady=(6, 0))
            ctk.CTkLabel(ent, text=desc, font=font(11), text_color=MUTED,
                         wraplength=190, justify="left").pack(anchor="w")

            def surligner(_e, c=card, on=True):
                c.configure(border_color=(PALETTE["primary"] if on else BORDER[0] if ctk.get_appearance_mode() == "Light" else BORDER[1]))

            for w in (card, ent) + tuple(ent.winfo_children()):
                w.bind("<Enter>", lambda e, c=card: surligner(e, c, True))
                w.bind("<Leave>", lambda e, c=card: surligner(e, c, False))
                w.bind("<Button-1>", lambda _e, c=cmd: c())

        # ================= PIED DE PAGE =================
        ctk.CTkFrame(scroll, fg_color="transparent", height=10).pack()
        foot = ctk.CTkFrame(scroll, fg_color="transparent")
        foot.pack(fill="x", padx=24, pady=(8, 14))
        ctk.CTkFrame(foot, height=1, fg_color=BORDER).pack(fill="x")
        ctk.CTkLabel(foot, text="OFPPT  ·  Complexe de Formation Professionnelle de Berkane  ·  Gestion Administrative",
                     font=font(11), text_color=MUTED).pack(pady=(8, 0))

    # --- PAGE FORMATEURS : PERSONNEL ET VACATAIRES ---
    def show_formateurs(self):
        """Point d'entrée unique pour gérer les formateurs permanents et vacataires."""
        self.clear_main_frame()

        title = ctk.CTkLabel(
            self.main_frame,
            text="Gestion des Formateurs",
            font=ctk.CTkFont(size=22, weight="bold")
        )
        title.pack(anchor="w", padx=20, pady=(18, 4))

        subtitle = ctk.CTkLabel(
            self.main_frame,
            text="Formateurs permanents (fonction « formateur ») et formateurs vacataires. "
                 "Les administrateurs et autres agents se gèrent dans la rubrique Personnel.",
            font=ctk.CTkFont(size=13), wraplength=900, justify="left"
        )
        subtitle.pack(anchor="w", padx=20, pady=(0, 15))

        with get_db_connection() as conn:
            cur = conn.cursor()
            cur.execute("SELECT COUNT(*) FROM personnel WHERE fonction LIKE '%formateur%'")
            nb_formateurs = cur.fetchone()[0]
            cur.execute("SELECT COUNT(*) FROM vacataires")
            nb_vacataires = cur.fetchone()[0]

        cards = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        cards.pack(fill="x", padx=20, pady=10)
        cards.grid_columnconfigure((0, 1), weight=1)

        def card(col, titre, description, total, open_cmd, import_cmd, export_cmd):
            box = ctk.CTkFrame(cards, corner_radius=12, border_width=1, border_color="#d5dce5")
            box.grid(row=0, column=col, sticky="nsew", padx=8, pady=8)
            ctk.CTkLabel(box, text=titre, font=ctk.CTkFont(size=17, weight="bold")).pack(anchor="w", padx=18, pady=(16, 4))
            ctk.CTkLabel(box, text=description, justify="left", wraplength=360).pack(anchor="w", padx=18, pady=4)
            ctk.CTkLabel(box, text=f"{total} enregistrement(s)", font=ctk.CTkFont(size=14, weight="bold"), text_color=MAIN_COLOR).pack(anchor="w", padx=18, pady=8)
            actions = ctk.CTkFrame(box, fg_color="transparent")
            actions.pack(fill="x", padx=12, pady=(4, 16))
            ctk.CTkButton(actions, text="Gérer", command=open_cmd, width=100, fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8).pack(side="left", padx=4)
            ctk.CTkButton(actions, text="Importer Excel", command=import_cmd, width=120, fg_color="#217346", hover_color="#145a30").pack(side="left", padx=4)
            ctk.CTkButton(actions, text="Exporter Excel", command=export_cmd, width=120, fg_color="#217346", hover_color="#145a30").pack(side="left", padx=4)

        card(0, "Formateurs permanents", "Agents dont la fonction est « formateur ».", nb_formateurs,
             lambda: self.show_personnel("formateur"), self.import_excel, self.export_personnel_excel)
        card(1, "Formateurs vacataires", "Intervenants vacataires avec CIN, MHA, statut et affectation.", nb_vacataires,
             self.show_vacataires, self.import_vacataires_excel, self.export_vacataires_excel)

        note = ctk.CTkFrame(self.main_frame, corner_radius=10)
        note.pack(fill="x", padx=28, pady=20)
        ctk.CTkLabel(note, text="Conseil", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w", padx=15, pady=(12, 3))
        ctk.CTkLabel(note, text="Utilisez les modèles Excel disponibles dans la rubrique vacataires et gardez un CIN unique pour éviter les doublons.", justify="left", wraplength=900).pack(anchor="w", padx=15, pady=(0, 12))

    # --- PAGE PERSONNEL ---
    def show_personnel(self, filtre_fonction=None):
        """Liste du personnel. filtre_fonction="formateur" -> uniquement les formateurs ;
        sans filtre -> tout le monde (formateurs, administrateurs, autres agents)."""
        self._perso_filtre = filtre_fonction
        self.clear_main_frame()

        top_frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        top_frame.pack(fill="x", padx=20, pady=10)

        titre_perso = "Liste des Formateurs" if getattr(self, "_perso_filtre", None) else "Liste du Personnel"
        title = ctk.CTkLabel(top_frame, text=titre_perso, font=ctk.CTkFont(size=20, weight="bold"))
        title.pack(side="left")

        btn_import = ctk.CTkButton(top_frame, text="Importer Excel", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.import_excel)
        btn_import.pack(side="right", padx=5)

        btn_export = ctk.CTkButton(top_frame, text="Exporter Excel", fg_color="#217346", hover_color="#145a30", command=self.export_personnel_excel)
        btn_export.pack(side="right", padx=5)

        btn_add = ctk.CTkButton(top_frame, text="+ Ajouter Personnel", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=lambda: AddPersonnelWindow(self, self.load_personnel))
        btn_add.pack(side="right", padx=5)

        search_frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        search_frame.pack(fill="x", padx=20, pady=5)

        self.search_entry = ctk.CTkEntry(search_frame, placeholder_text="Rechercher par Nom, Prénom ou CIN...")
        self.search_entry.pack(side="left", expand=True, fill="x", padx=(0, 10))
        self.search_entry.bind("<KeyRelease>", lambda e: self.load_personnel())

        self.scroll_personnel = ctk.CTkScrollableFrame(self.main_frame)
        self.scroll_personnel.pack(fill="both", expand=True, padx=20, pady=10)

        self.load_personnel()

    def personnel_actions_popup(self, data):
        """Fenetre d'actions d'un agent (ouverte par double-clic sur sa carte)."""
        win = ctk.CTkToplevel(self)
        win.title(f"{data[1]} {data[2]}")
        win.geometry("330x410")
        win.grab_set()
        ctk.CTkLabel(win, text=f"{(data[1] or '').upper()} {data[2] or ''}",
                     font=ctk.CTkFont(size=17, weight="bold")).pack(pady=(18, 4))
        ctk.CTkLabel(win, text=f"CIN : {data[3] or 'N/A'}   ·   {data[4] or '—'}",
                     font=ctk.CTkFont(size=11), text_color="#6b7a89").pack(pady=(0, 10))
        actions = [("📄  Attestation de travail", lambda: self.generate_attestation_pdf(data)),
                   ("💰  Attestation de salaire", lambda: self.generate_attestation_salaire_pdf(data)),
                   ("🧾  Bulletin de paie", lambda: BulletinPaieWindow(self, data, self.load_personnel)),
                   ("✈️  Ordre de mission", lambda: OrdreMissionDialog(self, data, self.generate_om_pdf)),
                   ("✏️  Modifier", lambda: EditPersonnelWindow(self, data, self.load_personnel)),
                   ("🗑  Supprimer", lambda: self.delete_personnel(data[0]))]
        for txt, cmd in actions:
            ctk.CTkButton(win, text=txt, font=ctk.CTkFont(size=13, weight="bold"),
                          fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8,
                          command=lambda c=cmd, w=win: (w.destroy(), c())
                          ).pack(fill="x", padx=25, pady=5)

    def load_personnel(self):
        for widget in self.scroll_personnel.winfo_children():
            widget.destroy()

        query = self.search_entry.get().strip()
        with get_db_connection() as conn:
            cursor = conn.cursor()

            only_form = getattr(self, "_perso_filtre", None) == "formateur"
            if query and only_form:
                cursor.execute('''
                    SELECT id, nom, prenom, cin, specialite, fonction, echelle, categorie 
                    FROM personnel 
                    WHERE fonction LIKE '%formateur%' AND (nom LIKE ? OR prenom LIKE ? OR cin LIKE ?)
                ''', (f"%{query}%", f"%{query}%", f"%{query}%"))
            elif query:
                cursor.execute('''
                    SELECT id, nom, prenom, cin, specialite, fonction, echelle, categorie 
                    FROM personnel 
                    WHERE nom LIKE ? OR prenom LIKE ? OR cin LIKE ?
                ''', (f"%{query}%", f"%{query}%", f"%{query}%"))
            elif only_form:
                cursor.execute("""SELECT id, nom, prenom, cin, specialite, fonction, echelle, categorie 
                                  FROM personnel WHERE fonction LIKE '%formateur%'""")
            else:
                cursor.execute('SELECT id, nom, prenom, cin, specialite, fonction, echelle, categorie FROM personnel')

            rows = cursor.fetchall()
            masses = dict(cursor.execute("SELECT id, masse_statutaire FROM personnel").fetchall())

        for row in rows:
            p_id, nom, prenom, cin, spec, fn, ech, cat = row

            card = ctk.CTkFrame(self.scroll_personnel)
            card.pack(fill="x", pady=5, padx=5)

            info_text = f"{nom.upper()} {prenom}"
            try:
                if masses.get(p_id):
                    info_text += f"   ·   {float(masses[p_id]):g} h/sem"
            except (TypeError, ValueError):
                pass
            lbl_info = ctk.CTkLabel(card, text=info_text, font=ctk.CTkFont(size=15, weight="bold"))
            lbl_info.pack(side="left", padx=15, pady=10)
            lbl_info.bind("<Double-Button-1>", lambda e, data=row: self.personnel_actions_popup(data))

            btns = ctk.CTkFrame(card, fg_color="transparent")
            btns.pack(side="right", padx=6, pady=6)
            actions = [("Attestation", 88, lambda d=row: self.generate_attestation_pdf(d)),
                       ("Salaire", 70, lambda d=row: self.generate_attestation_salaire_pdf(d)),
                       ("Bulletin", 72, lambda d=row: BulletinPaieWindow(self, d, self.load_personnel)),
                       ("Ordre mission", 100, lambda d=row: OrdreMissionDialog(self, d, self.generate_om_pdf)),
                       ("Modifier", 72, lambda d=row: EditPersonnelWindow(self, d, self.load_personnel)),
                       ("Supprimer", 80, "#a83232", "#7e2424", lambda d=row: self.delete_personnel(d[0]))]
            for item in actions:
                if len(item) == 3:
                    label, w, cmd = item
                    fg, hv = MAIN_COLOR, MAIN_COLOR_HOVER
                else:
                    label, w, fg, hv, cmd = item
                ctk.CTkButton(btns, text=label, width=w, height=28, corner_radius=8,
                              fg_color=fg, hover_color=hv,
                              font=ctk.CTkFont(size=11, weight="bold"),
                              command=lambda c=cmd: c()).pack(side="left", padx=2)    # --- PAGE SUIVI D'ABSENCE ---
    def show_suivi_absence(self):
        self.clear_main_frame()

        top_frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        top_frame.pack(fill="x", padx=20, pady=10)

        title = ctk.CTkLabel(top_frame, text="Suivi d'absence des Formateurs / Personnel", font=ctk.CTkFont(size=20, weight="bold"))
        title.pack(side="left")

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT id, nom, prenom FROM personnel ORDER BY nom ASC")
            self.personnel_list = cursor.fetchall()

        if not self.personnel_list:
            lbl_no_data = ctk.CTkLabel(self.main_frame, text="Aucun agent enregistré. Veuillez ajouter du personnel d'abord.", font=ctk.CTkFont(size=14))
            lbl_no_data.pack(pady=40)
            return

        self.personnel_map = {f"{p[1].upper()} {p[2]}": p[0] for p in self.personnel_list}

        select_frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        select_frame.pack(fill="x", padx=20, pady=5)

        lbl_select = ctk.CTkLabel(select_frame, text="Sélectionner un Formateur / Agent :", font=ctk.CTkFont(weight="bold"))
        lbl_select.pack(side="left", padx=(0, 10))

        self.combo_formateur = ctk.CTkOptionMenu(
            select_frame, 
            values=list(self.personnel_map.keys()), 
            fg_color=MAIN_COLOR, 
            button_color=MAIN_COLOR_HOVER,
            command=self.on_formateur_changed
        )
        self.combo_formateur.pack(side="left", fill="x", expand=True)

        frame_add = ctk.CTkFrame(self.main_frame, corner_radius=10)
        frame_add.pack(fill="x", padx=20, pady=10)

        lbl_add_title = ctk.CTkLabel(frame_add, text="Enregistrer une absence", font=ctk.CTkFont(size=14, weight="bold"))
        lbl_add_title.pack(anchor="w", padx=15, pady=(10, 5))

        frame_motif = ctk.CTkFrame(frame_add, fg_color="transparent")
        frame_motif.pack(fill="x", padx=15, pady=5)

        lbl_motif = ctk.CTkLabel(frame_motif, text="Raison / Motif :", font=ctk.CTkFont(weight="bold"))
        lbl_motif.pack(side="left", padx=(0, 10))

        self.motifs_menu = ABS_MOTIFS
        self.combo_motif_menu = ctk.CTkOptionMenu(
            frame_motif, 
            values=self.motifs_menu, 
            fg_color=MAIN_COLOR, 
            button_color=MAIN_COLOR_HOVER,
            command=self.on_motif_menu_change
        )
        self.combo_motif_menu.pack(side="left", fill="x", expand=True)

        self.frame_dates_menu = ctk.CTkFrame(frame_add, fg_color="transparent")
        self.frame_dates_menu.pack(fill="x", padx=15, pady=5)

        lbl_dep = ctk.CTkLabel(self.frame_dates_menu, text="Date Début :")
        lbl_dep.grid(row=0, column=0, padx=5, pady=5, sticky="w")

        self.cal_debut_menu = DateEntry(self.frame_dates_menu, date_pattern='dd/mm/yyyy', width=12, background=MAIN_COLOR, foreground='white', borderwidth=2)
        self.cal_debut_menu.grid(row=0, column=1, padx=5, pady=5)

        self.lbl_fin_menu = ctk.CTkLabel(self.frame_dates_menu, text="Date Fin :")
        self.lbl_fin_menu.grid(row=0, column=2, padx=(15, 5), pady=5, sticky="w")

        self.cal_fin_menu = DateEntry(self.frame_dates_menu, date_pattern='dd/mm/yyyy', width=12, background=MAIN_COLOR, foreground='white', borderwidth=2)
        self.cal_fin_menu.grid(row=0, column=3, padx=5, pady=5)

        self.frame_autre_menu = ctk.CTkFrame(frame_add, fg_color="transparent")        # motif libre (choix "Autre")
        ctk.CTkLabel(self.frame_autre_menu, text="Préciser la raison :").pack(side="left", padx=(5, 10))
        self.ent_autre_menu = ctk.CTkEntry(self.frame_autre_menu, placeholder_text="Ex : décès dans la famille, convocation...")
        self.ent_autre_menu.pack(side="left", fill="x", expand=True)

        btn_add = ctk.CTkButton(frame_add, text="Valider l'absence", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.enregistrer_absence_menu)
        btn_add.pack(pady=12)

        lbl_hist = ctk.CTkLabel(self.main_frame, text="Historique des absences du formateur sélectionné", font=ctk.CTkFont(size=14, weight="bold"))
        lbl_hist.pack(anchor="w", padx=20, pady=(10, 5))

        self.scroll_history_menu = ctk.CTkScrollableFrame(self.main_frame)
        self.scroll_history_menu.pack(fill="both", expand=True, padx=20, pady=(0, 15))

        self.on_motif_menu_change(self.combo_motif_menu.get())
        self.load_history_menu()

    def on_motif_menu_change(self, selected_motif):
        if absence_multi(selected_motif):
            self.lbl_fin_menu.grid()
            self.cal_fin_menu.grid()
        else:
            self.lbl_fin_menu.grid_remove()
            self.cal_fin_menu.grid_remove()
        if selected_motif == "Autre":
            self.frame_autre_menu.pack(fill="x", padx=15, pady=5, before=self.frame_dates_menu)
        else:
            self.frame_autre_menu.pack_forget()

    def on_formateur_changed(self, choice):
        self.load_history_menu()

    def enregistrer_absence_menu(self):
        selected_name = self.combo_formateur.get()
        p_id = self.personnel_map.get(selected_name)

        if not p_id:
            messagebox.showerror("Erreur", "Veuillez sélectionner un formateur.")
            return

        motif = self.combo_motif_menu.get()
        if motif == "Autre":
            txt_autre = self.ent_autre_menu.get().strip()
            if txt_autre:
                motif = f"Autre : {txt_autre}"
        date_deb = self.cal_debut_menu.get_date().strftime("%d/%m/%Y")

        if absence_multi(motif):
            if self.cal_fin_menu.get_date() < self.cal_debut_menu.get_date():
                messagebox.showerror("Erreur", "La date de fin ne peut pas être avant la date de début.")
                return
            date_f = self.cal_fin_menu.get_date().strftime("%d/%m/%Y")
        else:
            date_f = date_deb

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute('''
                INSERT INTO absences (personnel_id, motif, date_debut, date_fin)
                VALUES (?, ?, ?, ?)
            ''', (p_id, motif, date_deb, date_f))
            conn.commit()

        messagebox.showinfo("Succès", "Absence enregistrée avec succès !")
        self.load_history_menu()

    def load_history_menu(self):
        for widget in self.scroll_history_menu.winfo_children():
            widget.destroy()

        selected_name = self.combo_formateur.get()
        p_id = self.personnel_map.get(selected_name)

        if not p_id:
            return

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute('''
                SELECT id, motif, date_debut, date_fin 
                FROM absences 
                WHERE personnel_id=? 
                ORDER BY id DESC
            ''', (p_id,))
            rows = cursor.fetchall()

        if not rows:
            lbl_empty = ctk.CTkLabel(self.scroll_history_menu, text="Aucune absence enregistrée pour ce formateur.", font=ctk.CTkFont(slant="italic"))
            lbl_empty.pack(pady=20)
            return

        for row in rows:
            abs_id, motif, d_deb, d_fin = row
            card = ctk.CTkFrame(self.scroll_history_menu)
            card.pack(fill="x", pady=4, padx=5)

            txt_date = f"Du {d_deb} Au {d_fin}" if (absence_multi(motif) and d_deb != d_fin) else f"Le {d_deb}"
            info = f"Motif: {motif}  |  {txt_date}"
            lbl = ctk.CTkLabel(card, text=info, font=ctk.CTkFont(size=12, weight="bold"))
            lbl.pack(side="left", padx=10, pady=8)

            btn_del = ctk.CTkButton(card, text="Supprimer", fg_color="#a83232", hover_color="#7e2424", width=70, height=24, command=lambda id_=abs_id: self.delete_absence_menu(id_))
            btn_del.pack(side="right", padx=10, pady=8)

    def delete_absence_menu(self, abs_id):
        if messagebox.askyesno("Confirmation", "Voulez-vous supprimer cet enregistrement ?"):
            with get_db_connection() as conn:
                cursor = conn.cursor()
                cursor.execute("DELETE FROM absences WHERE id=?", (abs_id,))
                conn.commit()
            self.load_history_menu()

    # --- PAGE : FORMATEURS VACATAIRES ---
    # --- PAGE : FORMATEURS VACATAIRES (CIN, Nom et Prénom, MHA, Statut, Affectation) ---
    VAC_COLS = [("cin", "CIN"), ("nom", "Nom et Prénom"), ("mha", "MHA"), ("statut", "Statut"), ("affectation", "Affectation")]

    def show_vacataires(self):
        self.clear_main_frame()
        self.vac_edit_id = None

        top_frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        top_frame.pack(fill="x", padx=20, pady=10)
        ctk.CTkLabel(top_frame, text="Formateurs Vacataires", font=ctk.CTkFont(size=20, weight="bold")).pack(side="left")

        form = ctk.CTkFrame(self.main_frame, corner_radius=10)
        form.pack(fill="x", padx=20, pady=5)
        self.lbl_vac_form = ctk.CTkLabel(form, text="Ajouter un formateur vacataire", font=ctk.CTkFont(size=14, weight="bold"))
        self.lbl_vac_form.grid(row=0, column=0, columnspan=4, sticky="w", padx=15, pady=(10, 5))

        self.vac_entries = {}
        for i, (key, lab) in enumerate(self.VAC_COLS):
            r, c = 1 + i // 2, (i % 2) * 2
            ctk.CTkLabel(form, text=lab + " :", anchor="w", width=120).grid(row=r, column=c, padx=(15, 5), pady=4, sticky="w")
            e = ctk.CTkEntry(form, width=230)
            e.grid(row=r, column=c + 1, padx=(0, 15), pady=4, sticky="ew")
            self.vac_entries[key] = e
        form.grid_columnconfigure(1, weight=1)
        form.grid_columnconfigure(3, weight=1)

        btns = ctk.CTkFrame(form, fg_color="transparent")
        btns.grid(row=4, column=0, columnspan=4, pady=(10, 4))
        self.btn_vac_save = ctk.CTkButton(btns, text="Enregistrer", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.save_vacataire)
        self.btn_vac_save.pack(side="left", padx=5)
        ctk.CTkButton(btns, text="Vider", fg_color="#6c757d", hover_color="#495057", width=70, command=self.reset_vacataire_form).pack(side="left", padx=5)

        btns_excel = ctk.CTkFrame(form, fg_color="transparent")
        btns_excel.grid(row=5, column=0, columnspan=4, pady=(0, 10))
        ctk.CTkButton(btns_excel, text="📥  Importer Excel", fg_color="#217346", hover_color="#145a30",
                      width=160, command=self.import_vacataires_excel).pack(side="left", padx=5)
        ctk.CTkButton(btns_excel, text="📤  Exporter Excel", fg_color="#217346", hover_color="#145a30",
                      width=160, command=self.export_vacataires_excel).pack(side="left", padx=5)
        ctk.CTkButton(btns_excel, text="📋  Télécharger Modèle", fg_color="#1f538d", hover_color="#14375e",
                      width=180, command=self.download_vacataires_template).pack(side="left", padx=5)

        self.vac_search = ctk.CTkEntry(self.main_frame, placeholder_text="Rechercher par CIN, nom, statut ou affectation...")
        self.vac_search.pack(fill="x", padx=20, pady=(10, 0))
        self.vac_search.bind("<KeyRelease>", lambda e: self.load_vacataires())

        self.lbl_vac_total = ctk.CTkLabel(self.main_frame, text="", font=ctk.CTkFont(weight="bold"))
        self.lbl_vac_total.pack(anchor="w", padx=22, pady=(8, 0))

        self.scroll_vac = ctk.CTkScrollableFrame(self.main_frame)
        self.scroll_vac.pack(fill="both", expand=True, padx=20, pady=(5, 15))
        self.load_vacataires()

    def reset_vacataire_form(self):
        self.vac_edit_id = None
        for e in self.vac_entries.values():
            e.delete(0, "end")
        self.lbl_vac_form.configure(text="Ajouter un formateur vacataire")
        self.btn_vac_save.configure(text="Enregistrer")

    def save_vacataire(self):
        v = {k: e.get().strip() for k, e in self.vac_entries.items()}
        if not v["nom"]:
            messagebox.showerror("Erreur", "Le nom et prénom sont obligatoires.")
            return
        with get_db_connection() as conn:
            cursor = conn.cursor()
            if v["cin"]:
                cursor.execute("SELECT id FROM vacataires WHERE cin=? AND id<>?", (v["cin"], self.vac_edit_id or -1))
                if cursor.fetchone():
                    messagebox.showerror("Erreur", "Ce CIN existe déjà pour un autre formateur vacataire.")
                    return
            vals = (v["cin"], v["nom"], "", v["mha"], v["statut"], v["affectation"])
            if self.vac_edit_id:
                cursor.execute("UPDATE vacataires SET cin=?, nom=?, prenom=?, mha=?, statut=?, affectation=? WHERE id=?",
                               vals + (self.vac_edit_id,))
            else:
                cursor.execute("INSERT INTO vacataires (cin, nom, prenom, mha, statut, affectation) VALUES (?, ?, ?, ?, ?, ?)", vals)
            conn.commit()
        self.reset_vacataire_form()
        self.load_vacataires()

    def edit_vacataire(self, row):
        # row = (id, cin, nom et prenom, mha, statut, affectation)
        self.vac_edit_id = row[0]
        for key, val in zip([k for k, _ in self.VAC_COLS], row[1:]):
            e = self.vac_entries[key]
            e.delete(0, "end")
            if val not in (None, ""):
                e.insert(0, str(val))
        self.lbl_vac_form.configure(text="Modifier le formateur vacataire")
        self.btn_vac_save.configure(text="Mettre à jour")

    def delete_vacataire(self, v_id):
        if messagebox.askyesno("Confirmation", "Voulez-vous supprimer ce formateur vacataire ?"):
            with get_db_connection() as conn:
                conn.execute("DELETE FROM vacataires WHERE id=?", (v_id,))
                conn.commit()
            self.load_vacataires()

    def _vac_rows(self, q=""):
        """Retourne [(id, cin, nom et prenom, mha, statut, affectation)] (filtre optionnel)."""
        with get_db_connection() as conn:
            cursor = conn.cursor()
            base = "SELECT id, cin, nom, prenom, mha, statut, affectation FROM vacataires"
            if q:
                like = f"%{q}%"
                cursor.execute(base + " WHERE cin LIKE ? OR nom LIKE ? OR prenom LIKE ? OR statut LIKE ? OR affectation LIKE ? ORDER BY nom",
                               (like,) * 5)
            else:
                cursor.execute(base + " ORDER BY nom")
            rows = cursor.fetchall()
        return [(i, cin or "", f"{nom or ''} {prenom or ''}".strip(), mha or "", statut or "", aff or "")
                for i, cin, nom, prenom, mha, statut, aff in rows]

    def load_vacataires(self):
        for w in self.scroll_vac.winfo_children():
            w.destroy()
        rows = self._vac_rows(self.vac_search.get().strip())

        total_mha, has_mha = 0.0, False
        for r in rows:
            try:
                total_mha += float(str(r[3]).replace(",", "."))
                has_mha = True
            except ValueError:
                pass
        txt = f"{len(rows)} vacataire(s)"
        if has_mha:
            txt += f"  |  MHA totale : {total_mha:g}"
        self.lbl_vac_total.configure(text=txt)

        widths = [110, 0, 70, 120, 200]                     # CIN, Nom et Prénom (extensible), MHA, Statut, Affectation
        head = ctk.CTkFrame(self.scroll_vac, fg_color=MAIN_COLOR, corner_radius=8)
        head.pack(fill="x", pady=(2, 6), padx=5)
        for c, ((_, lab), w) in enumerate(zip(self.VAC_COLS, widths)):
            ctk.CTkLabel(head, text=lab, font=ctk.CTkFont(size=12, weight="bold"), text_color="white", anchor="w",
                         width=w or 10).grid(row=0, column=c, padx=(12, 6), pady=7, sticky="ew")
        head.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(head, text="", width=170).grid(row=0, column=5)

        if not rows:
            ctk.CTkLabel(self.scroll_vac, text="Aucun formateur vacataire enregistré.", font=ctk.CTkFont(slant="italic")).pack(pady=20)
            return
        for r in rows:
            card = ctk.CTkFrame(self.scroll_vac)
            card.pack(fill="x", pady=3, padx=5)
            card.grid_columnconfigure(1, weight=1)
            valeurs = [r[1] or "-", r[2].upper() if r[2] else "-", r[3] or "-", r[4] or "-", r[5] or "-"]
            for c, (val, w) in enumerate(zip(valeurs, widths)):
                ctk.CTkLabel(card, text=val, font=ctk.CTkFont(size=12, weight="bold" if c == 1 else "normal"), anchor="w",
                             width=w or 10, justify="left").grid(row=0, column=c, padx=(12, 6), pady=8, sticky="ew")
            actions = ctk.CTkFrame(card, fg_color="transparent", width=170)
            actions.grid(row=0, column=5, padx=(0, 8))
            ctk.CTkButton(actions, text="Modifier", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, width=70, height=24,
                          command=lambda row=r: self.edit_vacataire(row)).pack(side="left", padx=3)
            ctk.CTkButton(actions, text="Supprimer", fg_color="#a83232", hover_color="#7e2424", width=70, height=24,
                          command=lambda i=r[0]: self.delete_vacataire(i)).pack(side="left", padx=3)

    def _vac_style_sheet(self, ws, example_row=False):
        from openpyxl.styles import PatternFill, Font, Alignment, Border, Side
        header_fill = PatternFill("solid", fgColor="1F538D")
        thin = Border(left=Side(style="thin"), right=Side(style="thin"), top=Side(style="thin"), bottom=Side(style="thin"))
        for cell in ws[1]:
            cell.fill = header_fill
            cell.font = Font(color="FFFFFF", bold=True)
            cell.alignment = Alignment(horizontal="center", vertical="center")
            cell.border = thin
        for row_cells in ws.iter_rows(min_row=2):
            for cell in row_cells:
                cell.border = thin
                cell.alignment = Alignment(horizontal="center")
                if example_row:
                    cell.fill = PatternFill("solid", fgColor="D9EAD3")
                    cell.font = Font(italic=True, color="555555")
        for col in ws.columns:
            max_len = max((len(str(c.value or "")) for c in col), default=10)
            ws.column_dimensions[col[0].column_letter].width = min(max_len + 4, 40)

    def import_vacataires_excel(self):
        """Importe des formateurs vacataires (colonnes : CIN/Mle, Nom et Prénom, MHA, Statut, Affectation)."""
        import unicodedata
        chemin = filedialog.askopenfilename(
            title="Importer des vacataires depuis Excel",
            filetypes=[("Fichiers Excel", "*.xlsx *.xls"), ("Tous les fichiers", "*.*")]
        )
        if not chemin:
            return
        try:
            df = pd.read_excel(chemin, dtype=str)

            def norm(c):
                return unicodedata.normalize("NFKD", str(c)).encode("ascii", "ignore").decode().strip().lower()

            cols = {norm(c): c for c in df.columns}

            def find(*names):
                return next((cols[n] for n in names if n in cols), None)

            c_cin = find("cin", "mle", "matricule")
            c_full = find("nom et prenom", "nom & prenom", "nom complet")
            c_nom, c_pre = find("nom"), find("prenom")
            c_mha, c_stat, c_aff = find("mha"), find("statut"), find("affectation")
            if not (c_full or c_nom):
                messagebox.showerror("Erreur", "Colonne obligatoire manquante : 'Nom et Prénom'.\nVérifiez le modèle Excel.")
                return

            def val(row, col):
                if col is None:
                    return ""
                v = row.get(col)
                if v is None or (isinstance(v, float) and v != v):
                    return ""
                v = str(v).strip()
                return "" if v.lower() == "nan" else v

            with get_db_connection() as conn:
                cursor = conn.cursor()
                inseres, ignores = 0, 0
                for _, row in df.iterrows():
                    nom = val(row, c_full) or f"{val(row, c_nom)} {val(row, c_pre)}".strip()
                    cin = val(row, c_cin)
                    if not nom:
                        ignores += 1
                        continue
                    if cin:
                        cursor.execute("SELECT 1 FROM vacataires WHERE cin=?", (cin,))
                        if cursor.fetchone():
                            ignores += 1
                            continue
                    cursor.execute("INSERT INTO vacataires (cin, nom, prenom, mha, statut, affectation) VALUES (?, ?, '', ?, ?, ?)",
                                   (cin, nom, val(row, c_mha), val(row, c_stat), val(row, c_aff)))
                    inseres += 1
                conn.commit()
            messagebox.showinfo("Import terminé",
                                f"✅  {inseres} vacataire(s) importé(s) avec succès.\n"
                                f"⚠️  {ignores} ligne(s) ignorée(s) (CIN déjà existant ou nom manquant).")
            self.load_vacataires()
        except Exception as e:
            messagebox.showerror("Erreur d'importation", f"Impossible de lire le fichier :\n{e}")

    def export_vacataires_excel(self):
        """Exporte la liste des formateurs vacataires vers un fichier Excel."""
        chemin = filedialog.asksaveasfilename(
            title="Exporter les vacataires vers Excel",
            defaultextension=".xlsx",
            filetypes=[("Fichier Excel", "*.xlsx")],
            initialfile="Formateurs_Vacataires.xlsx"
        )
        if not chemin:
            return
        try:
            rows = self._vac_rows()
            if not rows:
                messagebox.showwarning("Export", "Aucun vacataire à exporter.")
                return
            df = pd.DataFrame([r[1:] for r in rows], columns=[lab for _, lab in self.VAC_COLS])
            with pd.ExcelWriter(chemin, engine="openpyxl") as writer:
                df.to_excel(writer, index=False, sheet_name="Vacataires")
                self._vac_style_sheet(writer.sheets["Vacataires"])
            messagebox.showinfo("Export réussi", f"✅  Fichier exporté avec succès :\n{chemin}")
            try:
                import subprocess, platform
                if platform.system() == "Windows":
                    subprocess.Popen(["start", "", chemin], shell=True)
            except Exception:
                logger.warning("Ouverture automatique du fichier impossible", exc_info=True)
        except Exception as e:
            messagebox.showerror("Erreur d'exportation", f"Impossible d'exporter :\n{e}")

    def download_vacataires_template(self):
        """Génère un fichier Excel modèle (CIN, Nom et Prénom, MHA, Statut, Affectation)."""
        chemin = filedialog.asksaveasfilename(
            title="Enregistrer le modèle Excel",
            defaultextension=".xlsx",
            filetypes=[("Fichier Excel", "*.xlsx")],
            initialfile="Modele_Vacataires.xlsx"
        )
        if not chemin:
            return
        try:
            df = pd.DataFrame(columns=[lab for _, lab in self.VAC_COLS])
            df.loc[0] = ["AB123456", "BENALI Ahmed", "60", "Vacataire", "CF Berkane"]
            with pd.ExcelWriter(chemin, engine="openpyxl") as writer:
                df.to_excel(writer, index=False, sheet_name="Vacataires")
                self._vac_style_sheet(writer.sheets["Vacataires"], example_row=True)
            messagebox.showinfo("Modèle créé",
                                f"✅  Modèle Excel créé avec succès :\n{chemin}\n\n"
                                "Remplissez les colonnes et utilisez 'Importer Excel' pour charger les données.")
            try:
                import subprocess, platform
                if platform.system() == "Windows":
                    subprocess.Popen(["start", "", chemin], shell=True)
            except Exception:
                logger.warning("Ouverture automatique du fichier impossible", exc_info=True)
        except Exception as e:
            messagebox.showerror("Erreur", f"Impossible de créer le modèle :\n{e}")

    # --- PAGE : FORMATION ---
    def show_formation(self):
        self.clear_main_frame()

        top_frame = ctk.CTkFrame(self.main_frame, fg_color="transparent")
        top_frame.pack(fill="x", padx=20, pady=10)

        title = ctk.CTkLabel(top_frame, text="Gestion et Planification des Formations", font=ctk.CTkFont(size=20, weight="bold"))
        title.pack(side="left")

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT id, nom, prenom FROM personnel ORDER BY nom ASC")
            self.personnel_formations = cursor.fetchall()

        if not self.personnel_formations:
            lbl_no_data = ctk.CTkLabel(self.main_frame, text="Aucun agent enregistré. Veuillez ajouter du personnel d'abord.", font=ctk.CTkFont(size=14))
            lbl_no_data.pack(pady=40)
            return

        ctk.CTkButton(top_frame, text="📥 Importer PDF / Excel", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER,
                      corner_radius=8, command=self.import_formations_file).pack(side="right")

        self.personnel_form_map = {f"{p[1].upper()} {p[2]}": p[0] for p in self.personnel_formations}

        form_frame = ctk.CTkFrame(self.main_frame, corner_radius=10)
        form_frame.pack(fill="x", padx=20, pady=10)

        lbl_form_title = ctk.CTkLabel(form_frame, text="Planifier une nouvelle formation", font=ctk.CTkFont(size=14, weight="bold"))
        lbl_form_title.pack(anchor="w", padx=15, pady=(10, 5))

        f_p = ctk.CTkFrame(form_frame, fg_color="transparent")
        f_p.pack(fill="x", padx=15, pady=4)
        ctk.CTkLabel(f_p, text="Personnel :", width=120, anchor="w", font=ctk.CTkFont(weight="bold")).pack(side="left")
        self.combo_form_perso = ctk.CTkOptionMenu(f_p, values=list(self.personnel_form_map.keys()), fg_color=MAIN_COLOR, button_color=MAIN_COLOR_HOVER)
        self.combo_form_perso.pack(side="left", fill="x", expand=True)

        f_t = ctk.CTkFrame(form_frame, fg_color="transparent")
        f_t.pack(fill="x", padx=15, pady=4)
        ctk.CTkLabel(f_t, text="Thème :", width=120, anchor="w", font=ctk.CTkFont(weight="bold")).pack(side="left")
        self.entry_form_theme = ctk.CTkEntry(f_t, placeholder_text="Ex: Management & Leadership")
        self.entry_form_theme.pack(side="left", fill="x", expand=True)

        f_l = ctk.CTkFrame(form_frame, fg_color="transparent")
        f_l.pack(fill="x", padx=15, pady=4)
        ctk.CTkLabel(f_l, text="Lieu :", width=120, anchor="w", font=ctk.CTkFont(weight="bold")).pack(side="left")
        self.entry_form_lieu = ctk.CTkComboBox(f_l, values=MOROCCO_CITIES, fg_color=("white", "#343638"),
                                               button_color=MAIN_COLOR, button_hover_color=MAIN_COLOR_HOVER, corner_radius=8)
        self.entry_form_lieu.set("")
        self.entry_form_lieu.pack(side="left", fill="x", expand=True)

        f_d = ctk.CTkFrame(form_frame, fg_color="transparent")
        f_d.pack(fill="x", padx=15, pady=4)
        ctk.CTkLabel(f_d, text="Dates :", width=120, anchor="w", font=ctk.CTkFont(weight="bold")).pack(side="left")
        
        ctk.CTkLabel(f_d, text="Début:").pack(side="left", padx=5)
        self.cal_form_debut = DateEntry(f_d, date_pattern='dd/mm/yyyy', width=10, background=MAIN_COLOR, foreground='white', borderwidth=2)
        self.cal_form_debut.pack(side="left", padx=5)

        ctk.CTkLabel(f_d, text="Fin:").pack(side="left", padx=(15, 5))
        self.cal_form_fin = DateEntry(f_d, date_pattern='dd/mm/yyyy', width=10, background=MAIN_COLOR, foreground='white', borderwidth=2)
        self.cal_form_fin.pack(side="left", padx=5)

        btn_save_form = ctk.CTkButton(form_frame, text="Enregistrer la formation", fg_color=MAIN_COLOR, hover_color=MAIN_COLOR_HOVER, corner_radius=8, command=self.save_formation)
        btn_save_form.pack(pady=12)

        lbl_h_form = ctk.CTkLabel(self.main_frame, text="Formations Planifiées", font=ctk.CTkFont(size=14, weight="bold"))
        lbl_h_form.pack(anchor="w", padx=20, pady=(10, 5))

        self.scroll_formations = ctk.CTkScrollableFrame(self.main_frame)
        self.scroll_formations.pack(fill="both", expand=True, padx=20, pady=(0, 15))

        self.load_formations_list()

    def _enregistrer_formation(self, cursor, p_id, perso_name, theme, lieu, dt_debut_obj, dt_fin_obj, avec_om=True):
        """Enregistre une formation + l'ordre de mission associe (utilise par la saisie manuelle et l'import PDF/Excel)."""
        d_debut = dt_debut_obj.strftime("%d/%m/%Y")
        d_fin = dt_fin_obj.strftime("%d/%m/%Y")

        # Regles de depart / retour selon la ville
        lieu_lower = lieu.lower()
        if "casa" in lieu_lower:
            om_date_dep, om_heure_dep = dt_debut_obj - timedelta(days=1), "06:00"
            om_date_ret, om_heure_ret = dt_fin_obj + timedelta(days=1), "20:00"
        elif "oujda" in lieu_lower or "nador" in lieu_lower:
            om_date_dep, om_heure_dep = dt_debut_obj, "06:00"
            om_date_ret, om_heure_ret = dt_fin_obj, "20:00"
        else:
            om_date_dep, om_heure_dep = dt_debut_obj, "08:00"
            om_date_ret, om_heure_ret = dt_fin_obj, "18:00"

        cursor.execute('''
            INSERT INTO formations (personnel_id, theme, lieu, date_debut, date_fin)
            VALUES (?, ?, ?, ?, ?)
        ''', (p_id, theme, lieu, d_debut, d_fin))
        formation_id = cursor.lastrowid

        if not avec_om:      # formation a distance (MS Teams) : pas de deplacement
            return

        cursor.execute('SELECT id, nom, prenom FROM personnel WHERE id=?', (p_id,))
        p = cursor.fetchone()
        nom_complet = f"{p[1].upper()} {p[2]}" if p else perso_name

        # Ordre de mission cree automatiquement avec les memes informations que la formation
        cursor.execute('''
            INSERT INTO ordres_mission (nom, motif, destination, transport, date_mission, personnel_id, formation_id,
                                        date_retour, heure_dep, heure_ret, num)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ''', (nom_complet, f"Participation à la formation : {theme}", lieu, "Public", om_date_dep.strftime("%d/%m/%Y"),
              p_id, formation_id, om_date_ret.strftime("%d/%m/%Y"), om_heure_dep, om_heure_ret, ""))

    def save_formation(self):
        perso_name = self.combo_form_perso.get()
        p_id = self.personnel_form_map.get(perso_name)
        theme = self.entry_form_theme.get().strip()
        lieu = self.entry_form_lieu.get().strip()
        dt_debut_obj = self.cal_form_debut.get_date()
        dt_fin_obj = self.cal_form_fin.get_date()
        d_debut = dt_debut_obj.strftime("%d/%m/%Y")
        d_fin = dt_fin_obj.strftime("%d/%m/%Y")

        if not p_id:
            messagebox.showerror("Erreur", "Veuillez sélectionner un membre du personnel.")
            return
        if dt_debut_obj > dt_fin_obj:
            messagebox.showerror("Erreur", "La date de début doit être antérieure ou égale à la date de fin.")
            return
        if not theme or not lieu:
            messagebox.showerror("Erreur", "Le thème et le lieu de la formation sont obligatoires.")
            return

        with get_db_connection() as conn:
            cursor = conn.cursor()
            self._enregistrer_formation(cursor, p_id, perso_name, theme, lieu, dt_debut_obj, dt_fin_obj)
            conn.commit()

        messagebox.showinfo("Succès", "Formation enregistrée avec succès !\n\nL'ordre de mission correspondant a été ajouté dans la rubrique « Ordre de mission ».")
        self.entry_form_theme.delete(0, 'end')
        self.entry_form_lieu.set("")
        self.load_formations_list()

    def load_formations_list(self):
        for widget in self.scroll_formations.winfo_children():
            widget.destroy()

        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute('''
                SELECT f.id, p.nom, p.prenom, f.theme, f.lieu, f.date_debut, f.date_fin 
                FROM formations f 
                JOIN personnel p ON f.personnel_id = p.id 
                ORDER BY f.id DESC
            ''')
            rows = cursor.fetchall()

        if not rows:
            lbl_empty = ctk.CTkLabel(self.scroll_formations, text="Aucune formation enregistrée.", font=ctk.CTkFont(slant="italic"))
            lbl_empty.pack(pady=20)
            return

        for row in rows:
            f_id, nom, prenom, theme, lieu, d_deb, d_fin = row
            card = ctk.CTkFrame(self.scroll_formations)
            card.pack(fill="x", pady=4, padx=5)

            info = f"{nom.upper()} {prenom} | Thème: {theme} | Lieu: {lieu} | Du {d_deb} au {d_fin}"
            lbl = ctk.CTkLabel(card, text=info, font=ctk.CTkFont(size=12, weight="bold"))
            lbl.pack(side="left", padx=10, pady=8)

            btn_del = ctk.CTkButton(card, text="Supprimer", fg_color="#a83232", hover_color="#7e2424", width=70, height=24, command=lambda id_=f_id: self.delete_formation(id_))
            btn_del.pack(side="right", padx=10, pady=8)

    def delete_formation(self, f_id):
        if messagebox.askyesno("Confirmation", "Voulez-vous supprimer cette formation ?"):
            with get_db_connection() as conn:
                cursor = conn.cursor()
                cursor.execute("DELETE FROM ordres_mission WHERE formation_id=?", (f_id,))
                cursor.execute("DELETE FROM formations WHERE id=?", (f_id,))
                conn.commit()
            self.load_formations_list()

    def import_formations_file(self):
        """Lit un PDF / Excel (meme scanne, par OCR) et ne propose que les formations du personnel enregistre."""
        path = filedialog.askopenfilename(
            title="Fichier des formations (PDF ou Excel)",
            filetypes=[("PDF / Excel / CSV", "*.pdf *.xlsx *.xls *.xlsm *.csv"), ("Tous les fichiers", "*.*")])
        if not path:
            return
        with get_db_connection() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, nom, prenom, cin FROM personnel")
            personnel = cur.fetchall()

        wait = ctk.CTkToplevel(self)
        wait.title("Lecture du fichier")
        wait.geometry("420x150")
        wait.resizable(False, False)
        wait.grab_set()
        lbl = ctk.CTkLabel(wait, text="Lecture du fichier en cours...\n(un PDF scanné peut prendre quelques minutes)",
                           font=ctk.CTkFont(size=13))
        lbl.pack(pady=(20, 10))
        bar = ctk.CTkProgressBar(wait, width=320)
        bar.set(0)
        bar.pack(pady=5)
        q = queue.Queue()

        def work():
            try:
                tables = read_formation_tables(path, progress=lambda i, n: q.put(("p", i, n)))
                matches, stats = match_formations(tables, personnel)
                q.put(("ok", matches, stats))
            except Exception as ex:
                logger.exception("Erreur import formations")
                q.put(("err", ex))

        def poll():
            done = None
            try:
                while True:
                    msg = q.get_nowait()
                    if msg[0] == "p" and msg[1] < 0:
                        lbl.configure(text="Préparation du moteur de lecture...\n(installation la première fois : "
                                           "quelques minutes, internet requis)")
                    elif msg[0] == "p":
                        bar.set(msg[1] / max(msg[2], 1))
                        lbl.configure(text=f"Lecture du PDF scanné (OCR) : {msg[1]} / {msg[2]} pages")
                    else:
                        done = msg
            except queue.Empty:
                pass
            if done is None:
                wait.after(250, poll)
                return
            wait.destroy()
            if done[0] == "err":
                messagebox.showerror("Erreur", f"Impossible de lire le fichier :\n{done[1]}")
            else:
                ImportFormationsWindow(self, done[1], done[2], path)

        threading.Thread(target=work, daemon=True).start()
        poll()

    def export_personnel_excel(self):
        """Exporte le personnel formateur vers un fichier Excel."""
        chemin = filedialog.asksaveasfilename(
            title="Exporter le personnel vers Excel",
            defaultextension=".xlsx",
            filetypes=[("Fichier Excel", "*.xlsx")],
            initialfile="Personnel_Formateurs.xlsx"
        )
        if not chemin:
            return
        try:
            with get_db_connection() as conn:
                rows = conn.execute(
                    "SELECT nom, prenom, cin, specialite, fonction, echelle, categorie FROM personnel ORDER BY nom, prenom"
                ).fetchall()
            if not rows:
                messagebox.showwarning("Export", "Aucun membre du personnel à exporter.")
                return
            columns = ["Nom", "Prénom", "CIN", "Spécialité", "Fonction", "Échelle", "Catégorie"]
            df = pd.DataFrame(rows, columns=columns)
            with pd.ExcelWriter(chemin, engine="openpyxl") as writer:
                df.to_excel(writer, index=False, sheet_name="Personnel")
                ws = writer.sheets["Personnel"]
                from openpyxl.styles import PatternFill, Font, Alignment, Border, Side
                fill = PatternFill("solid", fgColor="1F538D")
                thin = Side(style="thin", color="D9E2F3")
                for cell in ws[1]:
                    cell.fill = fill
                    cell.font = Font(color="FFFFFF", bold=True)
                    cell.alignment = Alignment(horizontal="center")
                    cell.border = Border(bottom=thin)
                for column in ws.columns:
                    max_len = max(len(str(cell.value or "")) for cell in column)
                    ws.column_dimensions[column[0].column_letter].width = min(max_len + 3, 35)
            messagebox.showinfo("Export réussi", f"Fichier exporté avec succès :\n{chemin}")
        except Exception as e:
            logger.exception("Erreur export personnel")
            messagebox.showerror("Erreur d'exportation", f"Impossible d'exporter :\n{e}")

    def import_excel(self):
        filepath = filedialog.askopenfilename(filetypes=[("Excel Files", "*.xlsx *.xls")])
        if not filepath:
            return

        try:
            df = pd.read_excel(filepath)
            added = 0
            with get_db_connection() as conn:
                cursor = conn.cursor()
                for _, row in df.iterrows():
                    nom = str(row.get('Nom', '')).strip()
                    prenom = str(row.get('Prénom', '')).strip()
                    cin = str(row.get('CIN', '')).strip()
                    spec = str(row.get('Spécialité', str(row.get('Poste', '')))).strip()

                    if nom and prenom and nom != 'nan' and prenom != 'nan':
                        try:
                            cursor.execute('''
                                INSERT INTO personnel (nom, prenom, cin, specialite) 
                                VALUES (?, ?, ?, ?)
                            ''', (nom, prenom, cin, spec))
                            added += 1
                        except sqlite3.IntegrityError:
                            pass
                conn.commit()
            messagebox.showinfo("Succès", f"{added} membre(s) du personnel importé(s) avec succès !")
            self.load_personnel()
        except Exception as e:
            messagebox.showerror("Erreur", f"Erreur lors de l'importation : {str(e)}")

    def delete_personnel(self, personnel_id):
        if messagebox.askyesno("Confirmation", "Voulez-vous vraiment supprimer cet agent ?"):
            with get_db_connection() as conn:
                cursor = conn.cursor()
                cursor.execute("DELETE FROM personnel WHERE id=?", (personnel_id,))
                conn.commit()
            self.load_personnel()

    def generate_attestation_pdf(self, personnel_data):
        pdf = PDF_Attestation()
        pdf.add_page()

        today_str = datetime.now().strftime("%d/%m/%Y")

        pdf.set_font("Arial", 'B', 10)
        et = get_etab()
        pdf.cell(110, 6, clean_str(f"OFP/DRO /{et['nom_court']}/ N°       /{datetime.now().year}"), align='L')
        pdf.cell(0, 6, clean_str(f"{et['ville']} le {today_str}"), align='R', ln=True)

        pdf.ln(15)

        pdf.set_font("Arial", 'B', 15)
        pdf.cell(0, 10, clean_str("ATTESTATION DE TRAVAIL"), align='C', ln=True)

        w_title = pdf.get_string_width("ATTESTATION DE TRAVAIL") + 6
        x_start = (210 - w_title) / 2
        pdf.line(x_start, pdf.get_y() - 2, x_start + w_title, pdf.get_y() - 2)

        pdf.ln(15)

        pdf.set_font("Arial", size=11)
        pdf.multi_cell(0, 7, clean_str(f"        Nous soussignés, Directeur de complexe de formation Professionnelle de {et['ville']}, atteste que :"))
        pdf.ln(10)

        nom_complet = f"{personnel_data[1].upper()} {personnel_data[2].upper()}"

        fields = [("M.", nom_complet)]
        if personnel_data[3] and str(personnel_data[3]).strip() and str(personnel_data[3]).lower() != "nan":
            fields.append(("Matricule", personnel_data[3]))
        if personnel_data[6] and str(personnel_data[6]).strip() and str(personnel_data[6]).lower() != "nan":
            fields.append(("Grade", personnel_data[6]))
        if personnel_data[5] and str(personnel_data[5]).strip() and str(personnel_data[5]).lower() != "nan":
            fields.append(("Fonction", personnel_data[5]))
        if personnel_data[7] and str(personnel_data[7]).strip() and str(personnel_data[7]).lower() != "nan":
            fields.append(("Lieu d'affectation", personnel_data[7]))

        left_margin = 25
        for label, val in fields:
            pdf.set_x(left_margin)
            pdf.set_font("Arial", size=10)
            pdf.cell(35, 7, clean_str(label), align='L')
            pdf.cell(5, 7, ":", align='C')
            pdf.set_font("Arial", 'B', 10)
            pdf.cell(0, 7, clean_str(val), align='L', ln=True)
            pdf.ln(2)

        pdf.ln(12)

        pdf.set_font("Arial", size=11)
        pdf.multi_cell(0, 6, clean_str("La présente attestation est délivrée à l'intéressé pour servir et valoir ce que de droit."))

        pdf.ln(20)

        pdf.set_font("Arial", 'B', 11)
        pdf.cell(0, 8, clean_str("Emargement du Directeur :"), align='C', ln=True)

        filename = f"Attestation_{personnel_data[1]}_{personnel_data[2]}.pdf"
        self.open_pdf_viewer(pdf, filename, "Attestation de Travail")

    def generate_attestation_salaire_pdf(self, personnel_data):
        """Attestation de salaire etablie a partir du BULLETIN DE PAIE scanne,
        selon le modele officiel OFPPT (compatible fpdf 1.x et 2.x)."""
        try:
            p_id = personnel_data[0]
            with get_db_connection() as conn:
                conn.execute(bulletin_create_sql())
                conn.commit()
                p = conn.execute("SELECT nom, prenom, cin, fonction FROM personnel WHERE id=?", (p_id,)).fetchone()
                b = fetch_bulletin(conn, p_id)
            if not p:
                messagebox.showerror("Erreur", "Agent introuvable.")
                return
            if not b:
                if messagebox.askyesno("Bulletin de paie manquant",
                                       "Aucun bulletin de paie n'est enregistré pour cet agent.\n\n"
                                       "Le saisir maintenant (à partir du bulletin scanné) ?"):
                    BulletinPaieWindow(self, personnel_data, self.load_personnel)
                return

            d = b
            nom, prenom, cin, fonction = p
            mois = d.get("mois") or mois_fr()

            _f = parse_money

            money = format_money

            def non_nul(v):
                return round(_f(v), 2) != 0

            GAIN_LINES = [("Salaire de Base", "salaire_base"), ("Rappel Salaire", "rappel_salaire"),
                          ("Heures Supplémentaires", "hrs_supp"),
                          ("Prime de Résidence", "prime_residence"), ("Rappel P.Residence", "rappel_p_residence"),
                          ("13 EME MOIS", "treizieme_mois"), ("Indemnité de Transport", "indemnite_transport"),
                          ("Indemnité de qualification", "indemnite_qualification"), ("Indemnité de logement", "indemnite_logement"),
                          ("Formation Alternée", "formation_alternee"), ("Indemnité spéciale", "indemnite_speciale"),
                          ("Alloc. Familiales", "alloc_familiales")]
            RET_LINES = [("Retraite RCAR", "rcar"), ("Mutuelle (ATLANTA)", "mutuelle"), ("I.R", "ir"),
                         ("Prêt Aid El Adha", "pret"), ("Assurance vie", "assurance_vie"), ("Retraite RECORE", "recore")]
            # les lignes dont la valeur est 0 (ou vide) ne sont pas affichees
            gains = [(l, d.get(k)) for l, k in GAIN_LINES if non_nul(d.get(k))]
            retenues = [(l, d.get(k)) for l, k in RET_LINES if non_nul(d.get(k))]
            # totaux recalcules a partir des lignes affichees (l'attestation est ainsi toujours coherente) ;
            # l'A.D.I. vient en deduction des retenues, comme sur le bulletin
            adi = round(_f(d.get("adi")), 2)
            tot_gains = round(sum(_f(d.get(k)) for _l, k in GAIN_LINES), 2)
            tot_ret = round(sum(_f(d.get(k)) for _l, k in RET_LINES) - adi, 2)
            net_paye = round(tot_gains - tot_ret, 2)

            pdf = PDF_Attestation_Salaire()
            pdf.fam = pdf.use_calibri()
            FAM = pdf.fam
            pdf.set_margins(25, 15, 25)
            pdf.set_auto_page_break(False)
            pdf.add_page()
            pdf.set_text_color(0, 0, 0)

            LM, RM = 25.0, 185.0      # marges 25 mm (modele Word)
            W = RM - LM
            LINE = 5.17               # hauteur d'une ligne du modele
            X_LIGNE = 40.875          # retrait 900 twips des lignes de detail
            X_TOTAL = 72.625          # retrait 2700 twips des totaux
            X_POINTS = 158.35         # fin des points de conduite (tab 7560)

            def setf(bold=False, italic=False, size=11):
                pdf.set_font(FAM, ("B" if bold else "") + ("I" if italic else ""), size)

            def sw(s, bold=False, italic=False, size=11):
                setf(bold, italic, size)
                return pdf.get_string_width(clean_str(s))

            def put(x, yy, s, bold=False, italic=False, size=11):
                setf(bold, italic, size)
                pdf.text(x, yy, clean_str(s))

            # reference + date (en gras comme dans le modele)
            now = datetime.now()
            etab = get_etab()
            put(LM, 63.8, f"REF : N° {etab['ref']} N°", bold=True)
            put(99.2, 63.8, f"/{now.year}", bold=True)
            dtxt = f"{etab['ville']}, le {now.strftime('%d/%m/%Y')}"
            put(RM - sw(dtxt, True), 63.8, dtxt, bold=True)

            # titre : gras, italique, souligne, centre
            ttl = "ATTESTATION DE SALAIRE"
            wt = sw(ttl, True, True)
            tx = (210 - wt) / 2
            put(tx, 79.4, ttl, True, True)
            pdf.set_draw_color(0, 0, 0)
            pdf.set_line_width(0.25)
            pdf.line(tx, 80.4, tx + wt, 80.4)

            # introduction justifiee (nom et fonction en gras)
            import unicodedata
            m0 = unicodedata.normalize("NFD", str(mois).strip()[:1].lower())[:1]
            de_mois = "d'" if m0 and m0 in "aeiouyh" else "de "
            segments = [
                ("Nous, soussigné Office de la Formation Professionnelle et de la Promotion du Travail, attestons que ", False),
                (f"M. {(nom or '').upper()} {(prenom or '').upper()},", True),
                (f" matricule {cin or '-'} est employé à notre organisme en qualité de ", False),
                (f"{fonction or 'Agent'}", True),
                (f" et perçoit un salaire mensuel (au titre du mois {de_mois}{mois}) détaillé comme suit :", False),
            ]
            mots = [(w_, b_) for seg, b_ in segments for w_ in seg.split()]
            spw = sw(" ")
            lignes, cur, curw = [], [], 0.0
            for wd, b_ in mots:
                ww = sw(wd, b_)
                add = ww if not cur else spw + ww
                if cur and curw + add > W:
                    lignes.append(cur); cur, curw, add = [], 0.0, ww
                cur.append((wd, b_, ww)); curw += add
            if cur:
                lignes.append(cur)
            y = 89.5
            for i, ln in enumerate(lignes):
                gap = spw
                if i < len(lignes) - 1 and len(ln) > 1:
                    gap = (W - sum(t[2] for t in ln)) / (len(ln) - 1)
                x = LM
                for wd, b_, ww in ln:
                    put(x, y, wd, b_)
                    x += ww + gap
                y += 5.2
            y = y - 5.2 + 2 * LINE      # ligne vide avant le detail

            def row(label, val, x0, bold=False, italic=False, neg=False):
                """Une ligne : libelle ...... montant DHS (montant aligne a droite)."""
                nonlocal y
                vt = ("- " if neg else "") + money(val, sep=bold) + " DHS"
                put(x0, y, label, bold, italic)
                vx = RM - sw(vt, bold, italic)
                debut = x0 + sw(label + " ", bold, italic)
                fin = min(X_POINTS, vx - 1.5)
                dw = sw(".", bold, italic)
                n = int((fin - debut) / dw) if dw else 0
                if n > 0:
                    put(debut, y, "." * n, bold, italic)
                put(vx, y, vt, bold, italic)
                y += LINE

            for lab, val in gains:
                row(lab, val, X_LIGNE)
            y += LINE
            row("TOTAL GAINS", "%.2f" % tot_gains, X_TOTAL, True, True)
            if retenues or adi:
                y += LINE
                for lab, val in retenues:
                    row(lab, val, X_LIGNE)
                if adi:
                    row("A.D.I. : tranche obligatoire", "%.2f" % adi, X_LIGNE, neg=True)
            if round(tot_ret, 2) != 0:
                y += LINE
                row("TOTAL RETENUES", "%.2f" % tot_ret, X_TOTAL, True, True)
            y += LINE
            row("NET A PAYER", "%.2f" % net_paye, X_TOTAL, True, True)
            y += LINE

            put(LM, y, "-L'intéressé perçoit une prime annuelle selon son rendement.")
            put(LM, y + 5.2, "-La présente attestation lui est délivrée pour servir et valoir ce que de droit.")

            filename = f"Attestation_Salaire_{nom}_{prenom}.pdf"
            self.open_pdf_viewer(pdf, filename, "Attestation de Salaire")
        except Exception as ex:
            logger.exception("Erreur attestation de salaire")
            messagebox.showerror("Erreur attestation de salaire",
                                 f"Une erreur est survenue :\n{ex}")

    def generate_om_pdf(self, personnel_data, om_data):
        try:
            nom_complet = f"{personnel_data[1].upper()} {personnel_data[2]}"
            with get_db_connection() as conn:
                cursor = conn.cursor()
                if om_data.get("om_id"):
                    # Ordre de mission deja cree (ex: depuis une formation) : on le met a jour, sans doublon
                    cursor.execute('''
                        UPDATE ordres_mission
                        SET motif=?, destination=?, transport=?, date_mission=?, date_retour=?,
                            heure_dep=?, heure_ret=?, num=?
                        WHERE id=?
                    ''', (om_data['motif'], om_data['destination'], om_data['transport_type'], om_data['date_dep'],
                          om_data['date_ret'], om_data['heure_dep'], om_data['heure_ret'], om_data['num'], om_data['om_id']))
                else:
                    cursor.execute('''
                        INSERT INTO ordres_mission (nom, motif, destination, transport, date_mission, personnel_id,
                                                    date_retour, heure_dep, heure_ret, num)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ''', (nom_complet, om_data['motif'], om_data['destination'], om_data['transport_type'], om_data['date_dep'],
                          personnel_data[0], om_data['date_ret'], om_data['heure_dep'], om_data['heure_ret'], om_data['num']))
                conn.commit()

            pdf = build_om_pdf(personnel_data, om_data, nom_complet)

            filename = f"Ordre_Mission_{personnel_data[1]}_{personnel_data[2]}.pdf"
            self.open_pdf_viewer(pdf, filename, "Ordre de Mission")

        except Exception as e:
            messagebox.showerror("Erreur", f"Impossible de générer l'ordre de mission : {str(e)}")


def launch_main_app():
    app = Application()
    app.mainloop()

if __name__ == "__main__":
    purge_temp_pdfs()      # supprime les anciens apercus PDF (donnees de paie)
    backup_data()          # copie de securite quotidienne de la base et de l'emploi du temps
    root = tk.Tk()
    root.withdraw()
    def _open_login():
        root.destroy()
        if not REQUIRE_LOGIN:
            launch_main_app()
            return
        login = LoginWindow(on_login_success=launch_main_app)
        login.mainloop()
    splash = SplashScreen(root, on_done_callback=_open_login)
    root.mainloop()
