; Script Inno Setup 6 - installateur OFPPT Gestion
; Les DONNEES (base, sauvegardes) sont dans %APPDATA%\MonLogicielGestion :
; elles ne sont JAMAIS touchees par l'installation, la mise a jour ou la desinstallation.

#define AppName "OFPPT Gestion"
#define AppVersion "1.0"
#define AppExe "OFPPT_Gestion.exe"

[Setup]
AppId={{7B1E2C4A-5D3F-4A8B-9C6E-0F1A2B3C4D5E}
AppName={#AppName}
AppVersion={#AppVersion}
AppPublisher=OFPPT
DefaultDirName={autopf}\{#AppName}
DefaultGroupName={#AppName}
OutputDir=Output
OutputBaseFilename=Setup_OFPPT_Gestion
SetupIconFile=app_icon.ico
UninstallDisplayIcon={app}\{#AppExe}
Compression=lzma2
SolidCompression=yes
WizardStyle=modern
ArchitecturesInstallIn64BitMode=x64compatible
PrivilegesRequiredOverridesAllowed=dialog
CloseApplications=yes

[Languages]
Name: "french"; MessagesFile: "compiler:Languages\French.isl"

[Tasks]
Name: "desktopicon"; Description: "Créer un raccourci sur le Bureau"; GroupDescription: "Raccourcis :"

[Files]
Source: "dist\OFPPT_Gestion\*"; DestDir: "{app}"; Flags: ignoreversion recursesubdirs createallsubdirs

[Icons]
Name: "{group}\{#AppName}"; Filename: "{app}\{#AppExe}"
Name: "{autodesktop}\{#AppName}"; Filename: "{app}\{#AppExe}"; Tasks: desktopicon

[Run]
Filename: "{app}\{#AppExe}"; Description: "Lancer {#AppName}"; Flags: nowait postinstall skipifsilent

; Aucune section [UninstallDelete] pour les donnees : la desinstallation conserve %APPDATA%\MonLogicielGestion
