# Skript

Skript is a Windows desktop application for professional screenwriting, story development and production planning. Version 1.0 includes screenplay editing, local project recovery, import and export tools, production planning and optional real-time collaboration.

## Install

Download the signed `Skript-Setup-1.0.0.4.exe` installer from the repository's Releases page. Skript supports Windows 10 and Windows 11 and uses Microsoft Edge or Google Chrome for its isolated desktop window.

The installer is per-user, normally requires no administrator access and includes Python plus the PDF, OCR and Word import/export engines. Verify the publisher shown by Windows before running a downloaded installer.

## Privacy

Scripts, preferences, recovery copies and backups remain on the user's computer unless the user explicitly starts a collaboration session or chooses a synchronised backup folder. PDF and modern Word imports are processed locally. Diagnostic reports exclude script text, project titles, usernames, email addresses and file paths.

## Running from source

1. Install Python 3.11 or newer.
2. Run `python scriptforge.py`.
3. Skript opens in an isolated desktop browser window and keeps project data locally.

PDF import uses the bundled PDF.js and Tesseract.js files in `vendor`; text extraction and English OCR for scanned pages run locally without uploading scripts or requiring a network connection.
Modern Word `.docx` imports are also processed locally. Legacy `.doc` imports use Microsoft Word or LibreOffice when either is installed.

## Tests

Install the JavaScript test dependencies with `pnpm install`, then run:

```powershell
pnpm e2e
```

The suite covers desktop and compact touch layouts, project workflows, import/export, editor behavior, accessibility and performance.

The same source checks and browser workflows run automatically for Windows release builds.

## Building

Build the Windows application from the repository root with PyInstaller:

```powershell
python tools/embed_html.py --check
pyinstaller --noconfirm --clean Skript.spec
```

The installer source is in `installer/`. Release installers are generated separately and are not committed to source control.

Public releases must be Authenticode-signed and timestamped. The release workflow refuses to create an unsigned tagged build. Certificate setup, local signing, signature verification, and Norton false-positive submission steps are documented in [RELEASE_SECURITY.md](RELEASE_SECURITY.md).

## Release information

- [Skript 1.0 official release notes](RELEASE_NOTES_1.0.0.4.md)
- [Release checklist](RELEASING.md)
- [Release signing and security](RELEASE_SECURITY.md)
- [Third-party notices](THIRD_PARTY_NOTICES.txt)

## Licence

Copyright © 2026 Jake McNeil. All rights reserved. This repository is source-visible proprietary software, not an open-source licence. See [LICENSE.txt](LICENSE.txt) for the applicable terms. Third-party components retain their own licences.

## Repository safety

Do not commit personal scripts, recovery data, collaboration secrets, signing certificates or generated release files. Security concerns should be reported using the guidance in [SECURITY.md](SECURITY.md).
