# Skript 1.0.0.1 Release Notes

## Tester hotfix

- Fixed a major graphics issue where the full-screen startup surface could remain as a dark layer behind the editor; startup now uses a compact centred splash that is withdrawn and compositor-flushed before the editor opens.
- PDF and browser-print exports no longer include the on-screen “Skip to script editor” link or floating View/zoom controls.
- Desktop mode now targets a centred 1920×1080 window and scales the same 16:9 shape to the computer's usable resolution; touch-capable devices retain the existing touch-friendly window sizing.
- Uncertain PDF imports now require the user to choose Film, TV, or Play, and the chosen format controls the imported project layout and element conventions.
- Importing a second PDF in the same session now reuses a stable bundled PDF worker instead of trying to fetch a temporary local worker module.
- Film and TV shooting-script scene numbers no longer cause the format detector to misidentify those PDFs as Stage Plays.
- Stage Play exports now follow BBC stage conventions: Roman-numbered acts, Arabic-numbered scenes, indented left-aligned character cues, dialogue beneath the cue, and mixed-case bracketed stage directions.
- Title-page contact and rights details are constrained to the bottom of the same title page and no longer spill onto a second page.
- Browser-print title pages now replace live input controls with wrapping print text and reset the on-screen cover wrapper, guaranteeing that the complete title page remains a single A4 PDF page.
- The Skript window is now forcibly centred as a landscape rectangle after Edge or Chrome opens, preventing saved browser placement from moving it back to the side of the desktop.
- Closing the Skript window now also stops its hidden local service, allowing the app to open again normally.
- Installation, update and repair now replace all old application files using a staged rollback-safe process.
- Running Skript is stopped before program files are replaced, preventing setup from hanging while updating the version.
- The setup window shows **Repair** when version 1.0.0.1 is already installed and repairs application files and shortcuts.
- Project files and user data in `Documents\ScriptForge` are never removed or replaced by install, update or repair.

## Fixes

- The desktop app now opens as a centred rectangular window instead of appearing against the left edge or starting maximised.
- The Backup Folder **+** button now uses a reliable native folder selector with a packaged Windows fallback.
- Secure collaboration link creation now allows more time on slower computers and falls back to a same-device listener when Windows blocks local-network sharing.
- Typing in large scripts is smoother because document statistics, scene navigation and character navigation updates are batched after short pauses instead of rebuilding on every keystroke.

## Interface changes

- The installer uses a rounded purple Install button matching the Skript brand.
- Options > About now includes **Changes**, showing the fixes and interface updates in the installed version.

## Release security

- Disabled UPX executable compression in Windows builds.
- Pinned PyInstaller and configured clean release builds to compile a project-specific bootloader, reducing reliance on a fingerprint shared by unrelated PyInstaller applications.
- Added SHA-256 Authenticode signing and RFC 3161 timestamping support for the application and installer.
- Tagged release builds now require configured signing credentials and verify both signatures before publishing.
- Added a documented Norton false-positive submission and release-hash process.

## Version

- Application, installer, executable metadata and setup filename updated from `1.0.0.0` to `1.0.0.1`.
