@echo off
chcp 65001 >nul
title Creation de l'installateur OFPPT
echo ============================================
echo   Creation de Setup_OFPPT_Gestion.exe
echo ============================================
echo.

where python >nul 2>nul || (echo Python n'est pas installe. Installez-le depuis python.org puis relancez. & pause & exit /b 1)

echo [1/3] Installation des modules necessaires...
python -m pip install -r requirements.txt || (echo Echec de l'installation des modules. & pause & exit /b 1)

echo.
echo [2/3] Creation du logiciel (PyInstaller)...
python -m PyInstaller --noconfirm --clean --onedir --windowed ^
  --name OFPPT_Gestion ^
  --icon app_icon.ico ^
  --add-data "logo_ofppt.png;." ^
  --collect-all customtkinter ^
  --collect-all tkcalendar ^
  --collect-all pdfplumber ^
  --collect-all fpdf ^
  --hidden-import babel.numbers ^
  --hidden-import openpyxl ^
  --hidden-import pypdf ^
  --hidden-import fitz ^
  --hidden-import pytesseract ^
  app.py || (echo Echec PyInstaller. & pause & exit /b 1)

echo.
echo [3/3] Creation du Setup.exe (Inno Setup)...
set ISCC="%ProgramFiles(x86)%\Inno Setup 6\ISCC.exe"
if not exist %ISCC% set ISCC="%ProgramFiles%\Inno Setup 6\ISCC.exe"
if not exist %ISCC% (
  echo Inno Setup 6 introuvable. Telechargez-le sur https://jrsoftware.org/isdl.php
  echo Le logiciel seul est pret dans dist\OFPPT_Gestion\OFPPT_Gestion.exe
  pause & exit /b 0
)
%ISCC% installer.iss || (echo Echec Inno Setup. & pause & exit /b 1)

echo.
echo Termine : Output\Setup_OFPPT_Gestion.exe
pause
