# -*- mode: python ; coding: utf-8 -*-

from pathlib import Path

# File/folder pickers rely on Tkinter. Stop the release immediately if the
# build environment can import the wrapper but cannot initialise Tcl data.
try:
    import tkinter as _build_tk
    _build_tcl = _build_tk.Tcl()
    _build_tcl.eval('info patchlevel')
except Exception as _tk_error:
    raise SystemExit(
        'Cannot build Skript: usable Tkinter/Tcl resources are required. '
        'Run the release build with normal filesystem access.'
    ) from _tk_error

project_root = Path(SPECPATH)

a = Analysis(
    [str(project_root / 'skript.py')],
    pathex=[str(project_root)],
    binaries=[],
    datas=[
        (str(project_root / 'vendor' / 'pdfjs'), 'vendor/pdfjs'),
        (str(project_root / 'vendor' / 'ocr'), 'vendor/ocr'),
        (str(project_root / 'assets' / 'skript-icon.png'), 'assets'),
        (str(project_root / 'assets' / 'skript.ico'), 'assets'),
        (str(project_root / 'VERSION.txt'), '.'),
        (str(project_root / 'THIRD_PARTY_NOTICES.txt'), '.'),
    ],
    hiddenimports=[
        'tkinter', 'tkinter.filedialog',
        'webview', 'webview.platforms.winforms', 'webview.platforms.edgechromium',
    ],
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
    [],
    exclude_binaries=True,
    name='Skript',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    icon=str(project_root / 'assets' / 'skript.ico'),
    version=str(project_root / 'installer' / 'skript_version_info.txt'),
    codesign_identity=None,
    entitlements_file=None,
    contents_directory='_runtime_1_1_0_0',
)

coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=False,
    upx_exclude=[],
    name='Skript',
)
