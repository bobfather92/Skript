# Skript 1.1 Roadmap

Skript 1.1 is planned as the first feature release after the stable 1.0 launch. The internal release target is `1.1.0.0`.

Development takes place on the `feature/1.1` branch. The stable 1.0 release remains on `main` until the 1.1 acceptance checks pass.

## 1. Multi-script projects

### Product model

A project is the overall production. It can contain one or more script documents, plus shared development and production documents such as the storyboard, shot list, outline, breakdown and call sheets.

Each script document keeps its own:

- title page and format;
- screenplay lines and revisions;
- import history;
- script-specific notes.

The project keeps shared:

- project title and identity;
- storyboard and media library;
- production planning documents;
- project-level notes and settings;
- an ordered list of its script documents.

### Delivery stages

1. **Batch import:** select several existing `.script` files in one operation and open every valid script as a document.
2. **Collection compatibility:** recognise the new `com.skript.project-collection` container and open all script documents stored inside it.
3. **Project navigation:** show the project name and its scripts clearly in the Navigator, with add, rename, reorder, duplicate and remove actions.
4. **Project save:** save and reopen the whole collection as one project without losing compatibility with individual 1.0 `.script` files.
5. **Import queue:** allow several Fountain, Final Draft, WriterDuet, PDF and Word files to be selected together, with a clear review queue for formats that need import confirmation.

The first two stages begin in the initial 1.1 development increment. The existing 1.0 single-script save format remains readable.

## 2. Storyboard Editor tools

The first Storyboard Editor expansion should focus on high-value editing work:

- multi-select cards and objects;
- duplicate, copy, paste and delete;
- undo and redo;
- drag-to-reorder scenes and shots;
- alignment, distribution, snap-to-grid and guides;
- zoom-to-fit and a compact overview;
- editable shot labels, captions, duration and status;
- bulk linking from script scenes;
- safer media replacement and missing-media reporting.

Deletion, undo/redo and save/reload behaviour must have automated regression coverage before new drawing or layout tools are added.

## 3. Writing suggestions

The 1.1 writing assistant should expand in three layers:

1. **Spelling:** stronger UK and US dictionaries, personal dictionary support, names and screenplay terminology.
2. **Grammar:** repeated words, agreement, punctuation, capitalisation, spacing and commonly confused words.
3. **Script flow:** repeated scene openings, long action blocks, dialogue density, character entrances, scene-heading consistency, pacing signals and possible continuity gaps.

Suggestions must:

- explain why they appeared;
- offer a safe one-click change where possible;
- be dismissible;
- avoid changing script text automatically;
- distinguish spelling, grammar and script-flow feedback;
- keep script analysis on the user's computer unless the user explicitly enables an online service.

## Acceptance gates

Before 1.1 is merged into `main`:

- 1.0 projects open without data loss;
- a project containing multiple scripts saves, closes and reopens correctly;
- failed files in a batch do not prevent valid files from opening;
- storyboard delete and undo/redo are covered by browser tests;
- writing suggestions never alter text without confirmation;
- the Windows installer, release notes and application all report the same final version;
- the complete automated test suite passes.
