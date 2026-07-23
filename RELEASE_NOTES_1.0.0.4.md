# Skript 1.0.0.4 — Official Release

Skript 1.0 is the first formal public release of the Windows desktop application for professional screenwriting, story development and production planning.

## Highlights

- Professional Film, Television and Stage Play editing with screenplay-aware formatting, pagination and navigation.
- Local project files, automatic recovery snapshots, dated recovery history and project-preserving backup handling.
- Local PDF and modern Word import, including offline English OCR for scanned PDFs and an import-review workflow for uncertain elements.
- PDF, Word, Final Draft and Fountain workflows with format and import metadata preserved through editing and reopening.
- Production tools including Stripboard, Shooting Schedule, Call Sheets, Production Catalogue, Sides/DOOD, Shot List and Storyboard linking.
- Writing and Production workspace modes, touch-friendly layouts, keyboard navigation, accessibility semantics and adaptive performance for large scripts.
- Privacy-safe problem reports that exclude script text, project titles, file paths, email addresses and usernames.

## Reliability and safety

- Recovery Centre can restore automatic snapshots and saved-project backups as separate unsaved projects.
- Repair, update and uninstall operations preserve scripts, backups and recovery copies.
- Versioned application runtime folders prevent locked old runtime files from blocking an update or repair.
- Local desktop API connections are reused to prevent loopback socket exhaustion during long editing and production sessions.
- The save-before-close workflow saves dirty projects before requesting the native Windows close action.

## System requirements

- Windows 10 or Windows 11.
- Microsoft Edge or Google Chrome.
- A per-user installation; administrator access is normally not required.

Python and the supported PDF, OCR and Word engines are included in the Windows package.

## Source verification

- 11 JavaScript regression suites passed.
- 9 Python regression suites passed.
- Complete browser workflow: 97 passed, 9 intentionally skipped, 0 failed across desktop and compact-touch configurations.
- Python compilation and embedded HTML syntax checks passed.

## Distribution gate

The public installer and application executable must be Authenticode-signed and timestamped. The tagged GitHub release workflow refuses to publish an unsigned release and verifies the expected publisher, certificate purpose, timestamp, installer lifecycle and SHA-256 checksum before producing release artifacts.

See [RELEASE_SECURITY.md](RELEASE_SECURITY.md) for publisher-signing and antivirus reputation guidance.
