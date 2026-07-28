# Skript 1.1.0.0 — Development Build

This is the first local development package on the road to Skript 1.1. It is intended for testing and is not the final public 1.1 release.

## Highlights

- Select several `.script`, `.sfg` or compatible JSON project files in one import operation.
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

- 11 JavaScript regression suites passed.
- 9 Python regression suites passed.
- Complete browser workflow: 101 passed, 9 intentionally skipped, 0 failed across desktop and compact-touch configurations.
- Python compilation and embedded HTML syntax checks passed.

## Development-build warning

The local package is unsigned and Windows will identify it as coming from an unknown publisher. It must not be uploaded as an official GitHub Release. The future public 1.1 installer and application executable must be Authenticode-signed and timestamped.

See [RELEASE_SECURITY.md](RELEASE_SECURITY.md) for publisher-signing and antivirus reputation guidance.
