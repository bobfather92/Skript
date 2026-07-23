# -*- mode: python ; coding: utf-8 -*-

from pathlib import Path

# A restricted build can import tkinter while still being unable to read its
# Tcl data files. PyInstaller would then silently exclude tkinter and produce
# an installer that only fails on the tester's machine. Refuse that build.
try:
    import tkinter as _build_tk
    _build_tcl = _build_tk.Tcl()
    _build_tcl.eval('info patchlevel')
except Exception as _tk_error:
    raise SystemExit(
        'Cannot build Skript Setup: usable Tkinter/Tcl resources are required. '
        'Run the release build with normal filesystem access.'
    ) from _tk_error

project_root = Path(SPECPATH)
payload = project_root / 'build_artifacts' / 'app' / 'Skript'

if not (payload / 'Skript.exe').exists():
    raise SystemExit('Build the Skript application payload before compiling the installer.')

a = Analysis(
    [str(project_root / 'installer' / 'skript_installer.py')],
    pathex=[str(project_root)],
    binaries=[],
    datas=[(str(payload), 'payload/Skript')],
    hiddenimports=['tkinter', 'tkinter.ttk', 'tkinter.messagebox'],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='Skript-Setup-1.0.0.4',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    icon=str(project_root / 'assets' / 'skript.ico'),
    version=str(project_root / 'installer' / 'setup_version_info.txt'),
    codesign_identity=None,
    entitlements_file=None,
)
