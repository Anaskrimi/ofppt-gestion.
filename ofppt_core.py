"""Infrastructure du logiciel, SANS interface graphique (testable seule) :
chemins et dossier de donnees, journal, base SQLite, sauvegardes, securite (mots de passe, tentatives de connexion),
montants, dates, texte des PDF, parametres de l'etablissement.

Ce fichier doit rester dans le MEME dossier que app.py."""
import os
import sys
import re
import json
import time
import shutil
import sqlite3
import hashlib
import hmac
import secrets
import logging
import tempfile
import unicodedata
from datetime import datetime

# Dossier des RESSOURCES (logo, polices) : dossier du programme, ou dossier interne une fois installe (PyInstaller).
BASE_DIR = getattr(sys, "_MEIPASS", None) or os.path.dirname(os.path.abspath(__file__))
APP_DATA_DIR = os.environ.get("OFPPT_APP_DATA") or os.path.join(os.getenv("APPDATA", BASE_DIR), "MonLogicielGestion")
os.makedirs(APP_DATA_DIR, exist_ok=True)

DB_FILE = os.path.join(APP_DATA_DIR, "database.db")
CRED_FILE = os.path.join(APP_DATA_DIR, "admin_cred.txt")
INITIAL_PASSWORD_FILE = os.path.join(APP_DATA_DIR, "admin_initial_password.txt")
ANALYSIS_SETTINGS_FILE = os.path.join(APP_DATA_DIR, "analysis_settings.json")
EMPLOI_FILE = os.path.join(APP_DATA_DIR, "emploi_data.json")      # module Emploi du temps (sauvegarde automatique)

# Migration automatique des fichiers existants du dossier local vers AppData
for _filename in ["database.db", "admin_cred.txt", "admin_initial_password.txt", "analysis_settings.json", "emploi_data.json"]:
    _old_path = os.path.join(BASE_DIR, _filename)
    _new_path = os.path.join(APP_DATA_DIR, _filename)
    if os.path.exists(_old_path) and not os.path.exists(_new_path):
        try:
            shutil.copy2(_old_path, _new_path)
        except Exception:
            pass

logging.basicConfig(
    filename=os.path.join(APP_DATA_DIR, "application.log"),
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(name)s: %(message)s",
)
logger = logging.getLogger("ofppt_app")

class _ClosingConnection(sqlite3.Connection):
    """Connexion SQLite FERMEE a la sortie du bloc `with` (sqlite3 se contente de valider/annuler)."""
    def __exit__(self, exc_type, exc, tb):
        try:
            return super().__exit__(exc_type, exc, tb)
        finally:
            self.close()


def get_db_connection():
    """Ouvre une connexion SQLite cohérente et active l'intégrité référentielle.
    A utiliser avec `with get_db_connection() as conn:` (valide, puis ferme la connexion)."""
    conn = sqlite3.connect(DB_FILE, factory=_ClosingConnection)
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA busy_timeout = 5000")
    return conn


def atomic_write_text(path, text):
    """Ecrit via un fichier temporaire puis os.replace : jamais de fichier a moitie ecrit
    (coupure, plantage ou disque plein pendant l'ecriture)."""
    tmp = f"{path}.tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write(text)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def atomic_write_json(path, data, **kw):
    atomic_write_text(path, json.dumps(data, ensure_ascii=False, **kw))


# --- SAUVEGARDES AUTOMATIQUES (base de donnees + emploi du temps) ---
BACKUP_DIR = os.path.join(APP_DATA_DIR, "backups")
BACKUP_KEEP = 10      # nombre de sauvegardes journalieres conservees pour chaque fichier


def backup_data():
    """Copie de securite dans AppData\\MonLogicielGestion\\backups :
    - une copie par jour (la premiere du jour), on garde les BACKUP_KEEP plus recentes ;
    - une copie « dernier » mise a jour a chaque appel.
    La base est copiee avec l'API sqlite3.backup (copie coherente, meme si elle est ouverte)."""
    try:
        os.makedirs(BACKUP_DIR, exist_ok=True)
        jour = datetime.now().strftime("%Y-%m-%d")
        cibles = []
        if os.path.exists(DB_FILE):
            cibles.append(("database", ".db", DB_FILE, True))
        if os.path.exists(EMPLOI_FILE):
            cibles.append(("emploi_data", ".json", EMPLOI_FILE, False))
        for nom, ext, src, is_db in cibles:
            for suffixe, ecraser in ((jour, False), ("dernier", True)):
                dest = os.path.join(BACKUP_DIR, f"{nom}_{suffixe}{ext}")
                if os.path.exists(dest) and not ecraser:
                    continue
                tmp = dest + ".tmp"
                if is_db:
                    s, d = sqlite3.connect(src), sqlite3.connect(tmp)
                    try:
                        s.backup(d)
                    finally:
                        d.close(); s.close()
                else:
                    shutil.copy2(src, tmp)
                os.replace(tmp, dest)
            anciennes = sorted(f for f in os.listdir(BACKUP_DIR) if re.fullmatch(rf"{nom}_\d{{4}}-\d{{2}}-\d{{2}}{re.escape(ext)}", f))
            for f in anciennes[:-BACKUP_KEEP]:
                os.remove(os.path.join(BACKUP_DIR, f))
    except Exception:
        logger.exception("Sauvegarde automatique impossible")


def latest_backup(nom, ext):
    """Chemin de la sauvegarde journaliere la plus recente (ou None)."""
    if not os.path.isdir(BACKUP_DIR):
        return None
    fs = sorted(f for f in os.listdir(BACKUP_DIR) if re.fullmatch(rf"{nom}_\d{{4}}-\d{{2}}-\d{{2}}{re.escape(ext)}", f))
    return os.path.join(BACKUP_DIR, fs[-1]) if fs else None


# Fichier simple pour stocker les identifiants admin modifiables
def _hash_password(password):
    """Hache un mot de passe avec PBKDF2-HMAC-SHA256."""
    if not isinstance(password, str):
        raise TypeError("Le mot de passe doit être une chaîne")
    salt = secrets.token_bytes(16)
    iterations = 300_000
    digest = hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), salt, iterations
    )
    return f"pbkdf2_sha256${iterations}${salt.hex()}${digest.hex()}"

def _verify_password(password, stored):
    """Vérifie les nouveaux hash PBKDF2 et les anciens hash SHA-256."""
    if not isinstance(password, str) or not isinstance(stored, str):
        return False
    try:
        if stored.startswith("pbkdf2_sha256$"):
            _, iterations, salt_hex, digest_hex = stored.split("$", 3)
            expected = hashlib.pbkdf2_hmac(
                "sha256", password.encode("utf-8"), bytes.fromhex(salt_hex), int(iterations)
            ).hex()
            return hmac.compare_digest(expected, digest_hex)

        # Compatibilité avec les fichiers créés par l'ancienne version.
        salt, digest = stored.split("$", 1)
        expected = hashlib.sha256((salt + password).encode("utf-8")).hexdigest()
        return hmac.compare_digest(expected, digest)
    except (ValueError, TypeError):
        logger.warning("Format de mot de passe invalide")
        return False

def get_admin_credentials():
    if os.path.exists(CRED_FILE):
        try:
            with open(CRED_FILE, "r", encoding="utf-8") as f:
                lines = f.read().splitlines()
                if len(lines) >= 2 and lines[0].strip() and lines[1].strip():
                    return lines[0].strip(), lines[1].strip()
        except OSError:
            logger.exception("Impossible de lire les identifiants administrateur")

    # Premier démarrage : générer un secret aléatoire et le déposer dans un
    # fichier local lisible uniquement par le compte système courant.
    default_user = "Anas"
    default_pass = os.environ.get("DEFAULT_ADMIN_PASSWORD") or secrets.token_urlsafe(12)
    save_admin_credentials(default_user, default_pass)
    try:
        with open(INITIAL_PASSWORD_FILE, "w", encoding="utf-8") as f:
            f.write(f"Utilisateur : {default_user}\nMot de passe initial : {default_pass}\n")
        os.chmod(INITIAL_PASSWORD_FILE, 0o600)
    except OSError:
        logger.exception("Impossible d'écrire le fichier du mot de passe initial")
    logger.warning("Identifiants administrateur initiaux créés pour %s", default_user)
    return default_user, get_admin_credentials()[1]

def save_admin_credentials(username, password):
    """Sauvegarde les identifiants avec un hash PBKDF2."""
    if not username or not password:
        raise ValueError("L'utilisateur et le mot de passe sont obligatoires")
    # Ne pas re-hacher un hash déjà sérialisé (usage interne uniquement).
    hashed = password if password.startswith("pbkdf2_sha256$") else _hash_password(password)
    atomic_write_text(CRED_FILE, f"{username.strip()}\n{hashed}\n")
    try:
        os.chmod(CRED_FILE, 0o600)
    except OSError:
        logger.warning("Impossible de restreindre les permissions de %s", CRED_FILE)


# ------------------------------------------------------------------
# TEXTE POUR LES PDF (polices standard FPDF = latin-1)
# ------------------------------------------------------------------
_TRANSLIT = str.maketrans({
    "\u2019": "'", "\u2018": "'", "\u201a": ",", "\u201b": "'", "\u201c": '"', "\u201d": '"', "\u201e": '"',
    "\u2013": "-", "\u2014": "-", "\u2212": "-", "\u2022": "-", "\u2026": "...",
    "\u0152": "OE", "\u0153": "oe", "\u20ac": "EUR", "\u202f": " ", "\u2009": " ", "\u200b": "", "\u200e": "", "\u200f": "",
    "\u0142": "l", "\u0141": "L", "\u0111": "d", "\u0110": "D", "\u0131": "i",
})


def _latin1_char(ch):
    try:
        ch.encode("latin-1")
        return ch
    except UnicodeEncodeError:
        base = "".join(c for c in unicodedata.normalize("NFKD", ch) if not unicodedata.combining(c))
        return base if base and all(ord(c) < 256 for c in base) else "?"


def clean_str(text):
    """Prepare un texte pour FPDF (latin-1) : les apostrophes/guillemets typographiques, tirets, oe, euro
    et lettres accentuees hors latin-1 sont remplaces par un equivalent au lieu de devenir « ? »."""
    if text is None:
        return ""
    return "".join(_latin1_char(c) for c in str(text).translate(_TRANSLIT))


# ------------------------------------------------------------------
# MONTANTS ET DATES
# ------------------------------------------------------------------
def parse_money(v, strict=False):
    """'1 234,56' / '1234.56' / '1.234,56' / '3663,00 DHS' / 12.5 / None -> float arrondi a 2 decimales.
    Vide -> 0.0. Valeur illisible -> 0.0, ou ValueError si strict=True."""
    if v is None or isinstance(v, bool):
        return 0.0
    if isinstance(v, (int, float)):
        f = float(v)
        if f != f or f in (float("inf"), float("-inf")):
            if strict:
                raise ValueError(f"montant invalide : {v!r}")
            return 0.0
        return round(f, 2)
    s = re.sub(r"(?i)\b(dhs?|mad)\b", "", str(v).replace("\u00a0", " ")).strip()
    s = s.replace(" ", "").replace("'", "")
    if not s:
        return 0.0
    if "," in s and "." in s:                      # 1.234,56 (europeen) ou 1,234.56 (anglo-saxon)
        s = s.replace(".", "").replace(",", ".") if s.rfind(",") > s.rfind(".") else s.replace(",", "")
    else:
        s = s.replace(",", ".")
    try:
        f = float(s)
        if f != f:
            raise ValueError
        return round(f, 2)
    except ValueError:
        if strict:
            raise ValueError(f"montant invalide : {v!r}")
        return 0.0


def format_money(v, sep=False):
    """3663.0 -> '3663,00' ; sep=True -> '12 482,74' (separateur de milliers)."""
    ent, dec = ("%.2f" % parse_money(v)).split(".")
    if sep:
        neg = ent.startswith("-")
        ent = ent.lstrip("-")
        parts = []
        while len(ent) > 3:
            parts.insert(0, ent[-3:]); ent = ent[:-3]
        parts.insert(0, ent)
        ent = ("-" if neg else "") + " ".join(parts)
    return f"{ent},{dec}"


MOIS_FR = ["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août",
           "septembre", "octobre", "novembre", "décembre"]


def mois_fr(dt=None):
    """'avril 2026' en francais, quelle que soit la langue de Windows (strftime('%B') depend de la locale)."""
    dt = dt or datetime.now()
    return f"{MOIS_FR[dt.month - 1]} {dt.year}"


# ------------------------------------------------------------------
# BULLETIN DE PAIE : montants en REAL (et non plus en texte) + migration
# ------------------------------------------------------------------
BULLETIN_MONEY_COLS = ["salaire_base", "rappel_salaire", "prime_residence", "rappel_p_residence", "treizieme_mois",
                       "indemnite_transport", "indemnite_qualification", "indemnite_logement", "formation_alternee",
                       "indemnite_speciale", "alloc_familiales", "hrs_supp", "adi", "rcar", "mutuelle", "ir", "pret",
                       "assurance_vie", "recore", "total_gains", "total_retenues", "net_a_payer"]
BULLETIN_COLS = ["personnel_id", "mois", "scan_path"] + BULLETIN_MONEY_COLS


def bulletin_create_sql(name="bulletin_paie"):
    money = ", ".join(f"{c} REAL" for c in BULLETIN_MONEY_COLS)
    return f"CREATE TABLE IF NOT EXISTS {name} (personnel_id INTEGER PRIMARY KEY, mois TEXT, scan_path TEXT, {money})"


def fetch_bulletin(conn, personnel_id):
    """Bulletin d'un agent sous forme de dictionnaire {colonne: valeur} (lecture PAR NOM de colonne,
    jamais par position : l'ordre des colonnes differe selon l'age de la base)."""
    cur = conn.execute("SELECT * FROM bulletin_paie WHERE personnel_id=?", (personnel_id,))
    row = cur.fetchone()
    if row is None:
        return None
    return dict(zip([c[0] for c in cur.description], row))


def migrate_bulletin_money(conn):
    """Version 1 du schema : convertit les montants TEXT de bulletin_paie en REAL.
    Reconstruit la table (dans une transaction) puis memorise la version dans PRAGMA user_version.
    Renvoie True si une migration a eu lieu."""
    if conn.execute("PRAGMA user_version").fetchone()[0] >= 1:
        return False
    try:
        existe = conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='bulletin_paie'").fetchone()
        if existe:
            cur = conn.execute("SELECT * FROM bulletin_paie")
            noms = [c[0] for c in cur.description]
            lignes = [dict(zip(noms, r)) for r in cur.fetchall()]
            conn.execute("DROP TABLE IF EXISTS bulletin_paie_old")
            conn.execute("ALTER TABLE bulletin_paie RENAME TO bulletin_paie_old")
            conn.execute(bulletin_create_sql())
            for d in lignes:
                vals = [d.get("personnel_id"), d.get("mois"), d.get("scan_path")] + \
                       [parse_money(d.get(c)) for c in BULLETIN_MONEY_COLS]
                conn.execute(f"INSERT INTO bulletin_paie ({', '.join(BULLETIN_COLS)}) "
                             f"VALUES ({','.join('?' * len(BULLETIN_COLS))})", vals)
            conn.execute("DROP TABLE bulletin_paie_old")
            logger.info("Migration bulletin_paie : %d ligne(s) converties en nombres", len(lignes))
        else:
            conn.execute(bulletin_create_sql())
        conn.execute("PRAGMA user_version = 1")
        conn.commit()
        return True
    except Exception:
        conn.rollback()
        logger.exception("Migration bulletin_paie impossible (l'ancienne table est conservee)")
        return False


# ------------------------------------------------------------------
# DONNEES DE L'ETABLISSEMENT (ex-textes « BERKANE » ecrits en dur dans les PDF)
# ------------------------------------------------------------------
ETAB_FILE = os.path.join(APP_DATA_DIR, "etablissement.json")
ETAB_DEFAULTS = {
    "complexe": "COMPLEXE DE FORMATION PROFESSIONNELLE BERKANE",
    "nom_court": "CF BERKANE",
    "ville": "Berkane",
    "adresse": "Route OUJDA Hay ED-DAKHLA BP 80  BERKANE",
    "tel": "(0536) 61.27.89",
    "fax": "(0536) 61.27.89",
    "ref": "OFPPT/DRO/CF BERKANE",
}
ETAB_LABELS = [("complexe", "Intitulé du complexe"), ("nom_court", "Nom court (pied de page)"), ("ville", "Ville"),
               ("adresse", "Adresse"), ("tel", "Téléphone"), ("fax", "Fax"), ("ref", "Préfixe des références")]


def get_etab():
    """Parametres de l'etablissement : valeurs par defaut completees par etablissement.json."""
    d = dict(ETAB_DEFAULTS)
    try:
        with open(ETAB_FILE, encoding="utf-8") as fh:
            x = json.load(fh)
        d.update({k: str(v) for k, v in x.items() if k in d and str(v).strip()})
    except FileNotFoundError:
        pass
    except Exception:
        logger.exception("etablissement.json illisible : valeurs par defaut utilisees")
    return d


def save_etab(values):
    atomic_write_json(ETAB_FILE, {k: str(values.get(k, "")).strip() for k in ETAB_DEFAULTS}, indent=2)


# ------------------------------------------------------------------
# CONNEXION : limitation des tentatives
# ------------------------------------------------------------------
LOGIN_STATE_FILE = os.path.join(APP_DATA_DIR, "login_state.json")
LOGIN_FREE_TRIES = 5          # echecs permis avant de ralentir
LOGIN_BASE_DELAY = 30         # secondes ; double a chaque echec supplementaire
LOGIN_MAX_DELAY = 900         # 15 minutes maximum


def _login_state():
    try:
        with open(LOGIN_STATE_FILE, encoding="utf-8") as fh:
            x = json.load(fh)
        return int(x.get("fails", 0)), float(x.get("last", 0))
    except Exception:
        return 0, 0.0


def login_wait_seconds(now=None):
    """Secondes a attendre avant une nouvelle tentative (0 si autorise)."""
    fails, last = _login_state()
    if fails < LOGIN_FREE_TRIES:
        return 0
    delay = min(LOGIN_MAX_DELAY, LOGIN_BASE_DELAY * 2 ** (fails - LOGIN_FREE_TRIES))
    return max(0, int(last + delay - (now if now is not None else time.time()) + 0.999))


def login_failed(now=None):
    fails, _ = _login_state()
    try:
        atomic_write_json(LOGIN_STATE_FILE, {"fails": fails + 1, "last": now if now is not None else time.time()})
    except OSError:
        logger.exception("Etat des tentatives de connexion non enregistre")


def login_succeeded():
    try:
        if os.path.exists(LOGIN_STATE_FILE):
            os.remove(LOGIN_STATE_FILE)
    except OSError:
        logger.warning("Etat des tentatives de connexion non supprime")


def password_needs_upgrade(stored):
    """True si le mot de passe est stocke dans l'ancien format SHA-256 (a re-hacher en PBKDF2 apres connexion)."""
    return isinstance(stored, str) and bool(stored) and not stored.startswith("pbkdf2_sha256$")


# ------------------------------------------------------------------
# APERCUS PDF TEMPORAIRES (donnees de paie : ne pas les laisser traîner)
# ------------------------------------------------------------------
TEMP_PDF_DIR = os.path.join(tempfile.gettempdir(), "OFPPT_apercus")


def temp_pdf_path(filename):
    os.makedirs(TEMP_PDF_DIR, exist_ok=True)
    return os.path.join(TEMP_PDF_DIR, os.path.basename(filename))


def purge_temp_pdfs(max_age_seconds=3600):
    """Supprime les apercus PDF temporaires de plus d'une heure (appele au demarrage)."""
    try:
        if not os.path.isdir(TEMP_PDF_DIR):
            return
        limite = time.time() - max_age_seconds
        for f in os.listdir(TEMP_PDF_DIR):
            p = os.path.join(TEMP_PDF_DIR, f)
            try:
                if os.path.isfile(p) and os.path.getmtime(p) < limite:
                    os.remove(p)
            except OSError:
                logger.warning("Apercu temporaire non supprime : %s", p)
    except Exception:
        logger.exception("Nettoyage des apercus temporaires impossible")
