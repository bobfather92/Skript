# -*- mode: python ; coding: utf-8 -*-

from pathlib import Path

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
    hiddenimports=['tkinter', 'tkinter.filedialog'],
    hookspath=[], hooksconfig={}, runtime_hooks=[], excludes=[], noarchive=False, optimize=0,
)
pyz = PYZ(a.pure)
exe = EXE(
    pyz, a.scripts, [], exclude_binaries=True, name='SkriptDiagnostic',
    debug=False, bootloader_ignore_signals=False, strip=False, upx=False,
    console=True, disable_windowed_traceback=False, argv_emulation=False,
    target_arch=None, icon=str(project_root / 'assets' / 'skript.ico'),
    codesign_identity=None, entitlements_file=None,
)
coll = COLLECT(exe, a.binaries, a.datas, strip=False, upx=False, upx_exclude=[], name='SkriptDiagnostic')
