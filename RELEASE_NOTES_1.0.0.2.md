# Skript 1.0.0.2 Release Notes

## Welcome and projects

- Added a **Recent projects** panel to the welcome screen so users can reopen recent work immediately.
- Added **Open Project** and **Browse another location** actions for finding Skript project files anywhere on the computer.
- Opening a recent or browsed project now closes the welcome screen automatically.

## Word import

- Added **Import Word** for `.docx` and legacy `.doc` documents.
- Word imports use the same review step as PDF imports so the user can confirm Film, TV or Stage Play formatting before adding the document to the editor.
- Modern `.docx` files are read directly by Skript's built-in offline reader and no longer depend on the desktop background service. Legacy `.doc` files are converted locally using Microsoft Word or LibreOffice when either is installed.
- Titles, title-page content, scene headings, action, characters, parentheticals and dialogue are carried into the import review where the source document provides enough structure.

## Appearance and Options

- Changed orange/yellow interface text, labels, active states and buttons to Skript purple while retaining red for genuine warnings and errors.
- Reduced the Page Break and Side-by-Side View glyphs so they remain inside the compact View control at different Windows display scales.
- Matched the **View changes** and **View licences** button widths in About.
- Added a version selector to Changes so the notes for 1.0.0.1 and 1.0.0.2 can be viewed separately.
- Updated the loading splash, About screen, application metadata and installer to version 1.0.0.2.

## Update and repair behaviour

- Installing 1.0.0.2 over an older release replaces the old application files and shortcuts while leaving users' project files untouched.
- If 1.0.0.2 is already installed, setup offers **Repair** to restore missing or damaged application files.
- The tester build remains unsigned. Windows or antivirus software may display a reputation warning until a production code-signing certificate is used and reputation is established.
