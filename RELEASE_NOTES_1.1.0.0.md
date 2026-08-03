# Skript 1.1.0.0 — Development Build

This is the first local development package on the road to Skript 1.1. It is intended for testing and is not the final public 1.1 release.

## Highlights

- Select several `.script`, `.sfg` or compatible JSON project files in one import operation.
- Import native WriterDuet `.wdz` checkpoint projects and WriterDuet JSON exports, including projects containing multiple script documents.
- Remove WriterDuet’s hidden character-name markers and recombine consecutive native dialogue fragments into one editable speech.
- Right-align screenplay transitions and import WriterDuet Act records as visible New Act elements that always begin a fresh page.
- Keep long imported dialogue as one selectable and editable Skript paragraph, including Word soft line breaks and dialogue that visually extends past a page.
- Export WriterDuet scripts with BBC-style A4 margins and 12-point spacing, proper continuation pages, top-right page headers, no browser-generated footers, and clean Act page breaks.
- Create and export Film, TV, BBC Radio Scene Style and BBC Stage scripts using the corresponding BBC layout conventions.
- Choose whether Notes elements are included in PDF, Word, Fountain, Final Draft and printed script output; Notes are excluded by default.
- Keep Edge's Downloads icon and browser controls hidden behind Skript's own Windows title bar.
- Replace Edge's unsaved-work box with a Skript exit window offering **Continue writing**, **Exit without saving**, and **Save and exit**.
- Block installation, update, repair and removal while any Skript version is open, requiring the user to save their work and close the app first.
- Hold and drag the entire Skript title bar using Windows' native window movement without blocking or destabilising the interface.
- Keep the title bar aligned to the visible window frame without extending into Windows' invisible resize border.
- Remove the duplicate/misaligned title bar on displays using Windows scaling, and keep Skript behind other applications when it is not active.
- Start each session in an isolated browser profile so Edge cannot restore stale duplicate Skript windows.
- Keep the Acts ribbon label aligned with File and Elements, and prevent double-clicking ribbon text from opening Edge's selection menu.
- Keep the editor surface fitted to the whole window after maximise, restore, title-bar double-click, or dragging directly from a maximised window.
- Preserve the rounded Windows outline around the active title bar and avoid repeatedly re-measuring or repositioning an unchanged window.
- Keep the minimise, maximise, and close controls inside the app frame immediately after resizing, maximising, restoring, or changing display scaling.
- Use Edge's genuine Windows titlebar exclusively, removing the separate foreground titlebar overlay and the duplicate in-page titlebar.
- Enter the reduced-memory performance profile when Windows reports severe memory pressure, even on a computer with otherwise capable hardware.
- Clear the Recent Projects history from either the welcome screen or Recent Projects window without deleting saved project files.
- Open all valid selected scripts even when another selected file is invalid.
- Open the initial `com.skript.project-collection` format containing multiple script documents.
- Access **Import Scripts…** directly from the Navigator's Add Document menu.
- Preserve a collection identity and title on every imported script document.
- Keep Recovery Centre keyboard focus reliable when it opens over the startup recovery prompt.

## Reliability and safety

- Existing Skript 1.0 project files remain readable.
- Multi-file imports remove only the initial blank document and do not overwrite authored work.
- Invalid files produce a clear summary without cancelling successful imports.
- The stable 1.0 release remains on `main`; 1.1 work remains isolated on `feature/1.1`.

## System requirements

- Windows 10 or Windows 11.
- Microsoft Edge or Google Chrome.
- A per-user installation; administrator access is normally not required.

Python and the supported PDF, OCR and Word engines are included in the Windows development package.

## Source verification

- 12 JavaScript regression suites passed.
- 9 Python regression suites passed.
- Complete browser workflow: 107 passed, 11 intentionally skipped, 0 failed across desktop and compact-touch configurations.
- Packaged Windows title-bar smoke test passed for hold-drag movement and visible-frame alignment.
- Python compilation and embedded HTML syntax checks passed.

## Development-build warning

The local package is unsigned and Windows will identify it as coming from an unknown publisher. It must not be uploaded as an official GitHub Release. The future public 1.1 installer and application executable must be Authenticode-signed and timestamped.

See [RELEASE_SECURITY.md](RELEASE_SECURITY.md) for publisher-signing and antivirus reputation guidance.
