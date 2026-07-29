import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { test, expect } from './support/fixtures.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));

test('Word exports retain BBC layout rules for screenplay, radio, and stage formats', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'desktop-chromium', 'DOCX layout is covered once on desktop');
  await skript.loadLocalFile(path.join(HERE, 'fixtures', 'loaded.script'));
  await skript.switchRibbon('export');

  const formats = [
    {
      format: 'film',
      title: 'BBC Screenplay Proof',
      lines: [
        ['new-act', 'ACT ONE'],
        ['transition', 'FADE IN:'],
        ['scene', 'EXT. LOCATION - DAY'],
        ['action', 'A quiet street wakes beneath a pale morning sky.'],
        ['character', 'MAYA'],
        ['parenthetical', '(quietly)'],
        ['dialogue', 'The first line of dialogue sits beneath the cue and remains a single editable paragraph.'],
        ['notes', 'Editorial note included only when requested.'],
        ['transition', 'CUT TO:'],
        ['new-act', 'ACT TWO'],
        ['scene', 'INT. NEWSROOM - NIGHT'],
        ['action', 'Phones ring across the room.'],
      ],
    },
    {
      format: 'audio',
      title: 'BBC Radio Proof',
      lines: [
        ['scene', 'SCENE 1.'],
        ['action', 'SFX: A HEAVY DOOR CLOSES.'],
        ['character', 'MAYA'],
        ['parenthetical', '(close)'],
        ['dialogue', 'The cue and this dialogue begin on the same line.'],
        ['transition', 'FADE.'],
        ['notes', 'Radio production note.'],
      ],
    },
    {
      format: 'play',
      title: 'BBC Stage Proof',
      lines: [
        ['act', 'ACT I'],
        ['scene', 'SCENE 1'],
        ['stage-direction', 'The lights rise slowly.'],
        ['character', 'MAYA'],
        ['dialogue', 'We begin.'],
        ['scene', 'SCENE 2'],
        ['stage-direction', 'A new morning.'],
        ['character', 'JO'],
        ['dialogue', 'And the next scene begins on a fresh page.'],
      ],
    },
  ];

  for (const sample of formats) {
    await page.evaluate(({ format, title, lines }) => {
      switchFormat(format, true);
      setCoverData(activeTabId, {
        title,
        author: 'Skript QA',
        contact1: 'writer@example.test',
        rights1: 'Copyright 2026',
      });
      const container = getLinesContainer(activeTabId);
      container.replaceChildren();
      for (const [type, text] of lines) {
        const line = addLine(activeTabId, type, container.lastElementChild, { deferStructure: true });
        line.textContent = text;
      }
      setExportNotesEnabled(true);
    }, sample);

    const downloadPromise = page.waitForEvent('download');
    await page.getByTestId('export-word').click();
    const download = await downloadPromise;
    const outputPath = testInfo.outputPath(`bbc-${sample.format}-proof.docx`);
    await download.saveAs(outputPath);
    const bytes = await fs.readFile(outputPath);
    expect(bytes.subarray(0, 2).toString('ascii')).toBe('PK');
    expect(bytes.length).toBeGreaterThan(1000);

    const documentXml = await page.evaluate(async values => {
      const archive = await docx.JSZip.loadAsync(new Uint8Array(values));
      return archive.file('word/document.xml').async('string');
    }, Array.from(bytes));
    expect(documentXml).toContain('w:w="11906"');
    expect(documentXml).toContain('w:h="16838"');
    const noteText = sample.lines.find(([type]) => type === 'notes')?.[1];
    if (noteText) expect(documentXml).toContain(noteText);
  }
});
