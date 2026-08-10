# Skript

Skript is a Windows desktop application for professional screenwriting, story development and production planning. Version 1.0 includes screenplay editing, local project recovery, import and export tools, production planning and optional real-time collaboration.

## Install

Download the signed `Skript-Setup-1.0.0.4.exe` installer from the repository's Releases page. Skript supports Windows 10 and Windows 11 and uses Microsoft Edge WebView2 inside its own native desktop window.

The installer is per-user, normally requires no administrator access and includes Python plus the PDF, OCR and Word import/export engines. Verify the publisher shown by Windows before running a downloaded installer.

## Privacy

Scripts, preferences, recovery copies and backups remain on the user's computer unless the user explicitly starts a collaboration session or chooses a synchronised backup folder. PDF and modern Word imports are processed locally. Diagnostic reports exclude script text, project titles, usernames, email addresses and file paths.

## Running from source

1. Install Python 3.11 or newer.
2. Run `python skript.py`.
3. Skript opens in its native WebView2 desktop window and keeps project data locally.

PDF import uses the bundled PDF.js and Tesseract.js files in `vendor`; text extraction and English OCR for scanned pages run locally without uploading scripts or requiring a network connection.
Modern Word `.docx` imports are also processed locally. Legacy `.doc` imports use Microsoft Word or LibreOffice when either is installed.

## Tests

Install the JavaScript test dependencies with `pnpm install`, then run:

```powershell
pnpm e2e
```

The suite covers desktop and compact touch layouts, project workflows, import/export, editor behavior, accessibility and performance.

The same source checks and browser workflows run automatically for Windows release builds.

## Version 1.1 development

Version 1.1 is being developed on the `feature/1.1` branch. It now includes complete multi-script projects, WriterDuet import and major Storyboard Studio improvements. Richer spelling, grammar and script-flow suggestions continue in the staged [1.1 roadmap](ROADMAP_1.1.md).

## Building

Build the Windows application from the repository root with PyInstaller:

```powershell
python -m pip install -r requirements-desktop.txt
python tools/embed_html.py --check
pyinstaller --noconfirm --clean Skript.spec
```

## Release information

- [Skript 1.1 development notes](RELEASE_NOTES_1.1.0.0.md)
- [Release checklist](RELEASING.md)
- [Release signing and security](RELEASE_SECURITY.md)
- [Third-party notices](THIRD_PARTY_NOTICES.txt)

## Licence

Copyright © 2026 Jake McNeil. Skript is free and open-source software licensed under the [GNU General Public License v3.0](LICENSE). You may use, study, modify, and redistribute it under the terms of that licence. Third-party components retain their own licences.
