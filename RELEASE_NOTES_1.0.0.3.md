# Skript 1.0.0.3 — Tester Release

## Recovery and project safety

- Added reliable crash recovery with ten rapid rolling snapshots and dated recovery history.
- Added Help → Recovery Centre to browse and restore automatic recovery copies and saved-project backups.
- Recovery Centre remains usable when its optional history folder is unavailable or locked.
- Fixed the desktop service ending too early when Edge reuses an existing process, which made Recovery Centre report that the service was unavailable.
- Fixed Recovery Centre appearing behind the Welcome screen during startup; it now takes focus and restoring a copy closes Welcome.
- Recovery copies always open as separate unsaved projects and never overwrite the source file.
- Added per-project unsaved indicators and warnings before closing unsaved work.
- Repair, update and uninstall refuse unsafe targets and only replace the registered application folder.

## Better error reporting

- Errors now include a suggested next action.
- Added Help → Report a Problem.
- Added Copy diagnostic information and Save report options.
- Diagnostic information excludes script text, project titles, file paths, email addresses and usernames.

## Large-script performance

- Optimised bulk loading, typing, scrolling, word counting and Navigator updates for scripts with 150–300 scenes.
- Scene-heading edits now update only the corresponding Navigator entry instead of rebuilding the full list.
- Very large or measurably slow documents automatically use the reduced-effects performance profile while manual performance overrides remain respected.

## Import accuracy and consistency

- Expanded Film, TV and Stage Play detection using screenplay slugs, television act structure, stage vocabulary, front matter and dialogue patterns.
- Improved character, dialogue, action and transition recognition using neighbouring elements, repeated speakers, Unicode names, cue extensions, Word indentation/alignment and a wider transition vocabulary.
- Production labels and camera directions are protected from being mistaken for character names.
- Added a fourth import-review step that explains and flags lower-confidence element classifications.
- Preserves selected format, element types, import confidence decisions and source metadata through editing, project save/reopen and PDF export.
- Added local, offline English OCR for scanned and mixed PDFs. OCR confidence feeds into the existing import-review step, and long imports can be cancelled.

## Installer and release assurance

- Added an isolated final-installer lifecycle test covering clean install, first launch, reopen, same-version repair, update from an older version and uninstall.
- The lifecycle test proves that representative projects, backups and recovery copies remain byte-for-byte unchanged.
- Release signing now verifies the expected publisher, code-signing certificate purpose and RFC 3161 timestamp before publishing.
- Fixed Setup appearing stuck at **Replacing old application files** by replacing the slow Windows management query with direct bounded process handling and detaching Setup's working directory from the installed application folder.
- Setup now installs the application runtime in a versioned folder. If Windows or antivirus holds the old `_internal` folder open, Repair installs and validates the new runtime, completes normally, and removes the obsolete folder later instead of waiting indefinitely.
- Cleanup of incomplete staging and previous-version folders is best-effort and can no longer block a successful Repair or Update. Setup writes `%TEMP%\Skript-Setup.log` if diagnostic details are needed.
- Edge and Chrome are launched from a temporary working folder so they cannot retain the installed Skript application directory during a later Repair or Update.

## Welcome screen and Windows shell

- Replaced the temporary S badge on Welcome with the packaged Skript typewriter icon.
- Matched the Recent Projects panel width to the other Welcome cards and removed the duplicate Browse another location action.
- Restored the standard Microsoft Edge app-window frame after the custom titlebar caused rendering and interaction problems on tester systems.
- Skript no longer reparents, embeds, masks or overlays the browser window. This removes the nested-window failure, large coloured outer area, white-edge artefact and side-to-side content movement.
- Retained the centred 16:9 desktop sizing and existing touch-mode sizing while returning window movement, resizing, maximise, minimise and close controls to Windows.
- Corrected the default project location to `Documents\Skript\scripts`. Existing projects, backups, recovery copies and recent-project history are copied safely from `Documents\ScriptForge` on first launch; legacy originals are never deleted or overwritten.
- Added a Skript-owned close prompt with **Save and close**, **Close without saving** and **Cancel** whenever an open project contains work; the browser's generic close warning is no longer used.
- Simplified and realigned the save-before-closing prompt so its message and all three actions fit cleanly inside the dialog.
- Welcome now shows exactly the three most recent projects in a wider fixed panel with no internal scrollbar.
- Fixed a startup race that could replace a newly selected page-view mode with an older saved preference.
- Corrected transition placement so `CUT TO:` and other transitions appear at the left screenplay margin in the editor, Edge PDF export and fallback PDF output.

## Tester note

This is an unsigned tester build. Windows reputation warnings can still appear until the release is code-signed and has established publisher reputation.
