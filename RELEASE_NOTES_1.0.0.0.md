# Skript 1.0.0.0 Release Candidate Notes

Build date: 2026-07-12

## Highlights

- Renamed the application to Skript and removed the old ScriptForge Pro top bar.
- Added Writing and Production workspace modes to keep the default interface simpler.
- Added production tools: Stripboard, Shooting Schedule, Call Sheets, Production Catalogue, Sides/DOOD, revisions, outline timeline, continuity, distribution, TV workspace, writing goals, sprint timer, templates, global rename, review links, localisation/RTL support, and storyboard animatic support.
- Improved script formatting, pagination, margins, PDF/print parity, dual dialogue conversion, paragraph joins/splits, and import handling.
- Added FDX import/round-trip validation against real Final Draft/Fade In fixtures.
- Added real-time collaboration groundwork with secure links, presence, attributed edits, comments, and conflict-aware merging.
- Added performance and accessibility work for low-end, high-end, and touch devices, including low-power mode, 44px touch targets, skip links, live announcements, keyboard navigation, and modal focus handling.
- Bundled local PDF.js assets so standard PDF import no longer depends only on the CDN.
- Added a packaged PDF export fallback to avoid taking down the desktop service when headless browser PDF rendering is unavailable.
- Added a new typewriter-and-paper application icon for the EXE, taskbar, browser shell and installer.
- Added a per-user Windows setup application with Start Menu/desktop shortcuts and Windows uninstall registration.
- Added automatic setup checks for Windows compatibility, Edge/Chrome, loopback service access, write permissions, free disk space and bundled payload integrity.
- Fixed Launch Skript after installation by moving startup to a detached post-install worker after setup closes.
- Fixed the setup window height and DPI-aware sizing so Install and Cancel remain fully visible at Windows display scaling.
- Added an Open Source Licences viewer under Options and a distributable third-party notices file.

## Verification

- HTML inline script syntax: passed.
- Python compile: passed.
- Embedded HTML matches `ScriptForge.html`: passed.
- Desktop E2E production workflows: 8 passed.
- Full compact/touch E2E: 34 passed, 3 skipped.
- Fresh packaged app starts and responds on `/api/version`: passed using diagnostic mode while the source copy was already running.
- Packaged favicon endpoint returns the new PNG asset: passed.
- EXE and setup version metadata: passed (`1.0.0.0`).
- Clean Windows application and setup compilation: passed.
- Automated prerequisite scan and bundled component verification: passed.
- Silent install, Start Menu shortcut and Windows uninstall registration: passed.
- Launch after installation and packaged local service response: passed.
- Uninstall cleanup of application files, shortcuts and registry entry: passed.
- Packaged setup visual verification at 150% Windows display scaling: Install and Cancel buttons visible and inside the window.
- Options open-source licence viewer: passed on desktop and compact touch projects.

## Known Skips

- Compact/touch skips desktop-only import/export coverage.
- Real FDX corpus runs once on desktop, not both projects.

## Release Status

This package is an installer-verified release candidate. The remaining distribution concern is publisher signing: the setup EXE is not code-signed and Windows SmartScreen may identify it as an unknown publisher.

Recommended next step: code-sign the setup and application executables before broad public distribution.
