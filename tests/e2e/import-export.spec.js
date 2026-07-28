import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { test, expect } from './support/fixtures.js';


const HERE = path.dirname(fileURLToPath(import.meta.url));

async function completeImportReview(page) {
  await expect(page.locator('#pdf-review-wizard')).toHaveClass(/open/);
  const filmChoice = page.locator('input[name="pdf-r-format-choice"][value="film"]');
  if (await filmChoice.count()) await filmChoice.check();
  for (let step = 0; step < 4; step += 1) await page.locator('#pdf-review-next').click();
  await expect(page.locator('#pdf-review-wizard')).not.toHaveClass(/open/);
}

test('a user can import a Fountain screenplay', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'desktop-chromium', 'Import is covered once on desktop');
  const fixture = path.join(HERE, 'fixtures', 'import-sample.fountain');
  await skript.importFountain(fixture);
  await completeImportReview(page);

  await expect(page.locator('#tabs-container .tab')).toHaveCount(1);
  await expect(page.locator('.tab.active .tab-title')).toHaveText('E2E Fountain Import');
  await expect(skript.activeLines).toHaveCount(5);
  await expect(skript.activeLines).toHaveText([
    'INT. TEST LAB - DAY',
    'A monitor blinks.',
    'MAYA',
    'It works.',
    'CUT TO:',
  ]);
  await expect(skript.activeLines.nth(2)).toHaveAttribute('data-type', 'character');
  await expect(skript.activeLines.nth(3)).toHaveAttribute('data-type', 'dialogue');
  await expect(skript.activeLines.nth(4)).toHaveAttribute('data-type', 'transition');
  await expect(skript.activeLines.nth(4)).toHaveCSS('text-align', 'left');
});

test('import creates a new tab when the active script contains writing', async ({ page, skript }) => {
  const fixture = path.join(HERE, 'fixtures', 'import-sample.fountain');
  await skript.activeLines.first().fill('INT. EXISTING PROJECT - NIGHT');
  await skript.importFountain(fixture);
  await completeImportReview(page);

  await expect(page.locator('#tabs-container .tab')).toHaveCount(2);
  await expect(page.locator('.tab.active .tab-title')).toHaveText('E2E Fountain Import');
  await expect(page.locator('.script-panel:not(.active) .script-line')).toContainText(['INT. EXISTING PROJECT - NIGHT']);
});

test('a user can import several Skript files at once', async ({ page, skript }) => {
  const makeProject = (title, scene) => JSON.stringify({
    version: 6,
    title,
    cover: { title },
    lines: [{ type: 'scene', text: scene }],
  });

  await page.locator('#file-input').setInputFiles([
    {
      name: 'episode-one.script',
      mimeType: 'application/json',
      buffer: Buffer.from(makeProject('Episode One', 'INT. KITCHEN - DAY')),
    },
    {
      name: 'episode-two.script',
      mimeType: 'application/json',
      buffer: Buffer.from(makeProject('Episode Two', 'EXT. GARDEN - NIGHT')),
    },
  ]);

  await expect(page.locator('#tabs-container .tab')).toHaveCount(2);
  await expect(page.locator('#tabs-container .tab-title')).toHaveText(['Episode One', 'Episode Two']);
  await expect(page.locator('.tab.active .tab-title')).toHaveText('Episode Two');
  await expect(page.locator('.script-panel.active .script-line')).toHaveText('EXT. GARDEN - NIGHT');
});

test('a multi-script project collection opens every script document', async ({ page, skript }) => {
  const collection = {
    schema: 'com.skript.project-collection',
    version: 1,
    projectId: 'collection-e2e-series',
    title: 'E2E Series',
    scripts: [
      {
        version: 6,
        title: 'Pilot',
        cover: { title: 'Pilot' },
        lines: [{ type: 'scene', text: 'INT. WRITERS ROOM - DAY' }],
      },
      {
        version: 6,
        title: 'Episode Two',
        cover: { title: 'Episode Two' },
        lines: [{ type: 'scene', text: 'EXT. STUDIO - NIGHT' }],
      },
    ],
  };

  await page.locator('#file-input').setInputFiles({
    name: 'e2e-series.script',
    mimeType: 'application/json',
    buffer: Buffer.from(JSON.stringify(collection)),
  });

  await expect(page.locator('#tabs-container .tab-title')).toHaveText(['Pilot', 'Episode Two']);
  await expect.poll(() => page.evaluate(() => tabs.map(tab => tab.collectionId))).toEqual([
    'collection-e2e-series',
    'collection-e2e-series',
  ]);
  await expect.poll(() => page.evaluate(() => tabs.map(tab => tab.collectionTitle))).toEqual([
    'E2E Series',
    'E2E Series',
  ]);
});

test('a WriterDuet project imports every script from its WDZ archive', async ({ page, skript }) => {
  const writerDuetArchive = {
    metadata: {
      script_info: {
        project_name: 'WriterDuet E2E Series',
        script_title: 'Shared Working Title',
        script_author: 'E2E Writer',
      },
      b: {
        'pilot-branch': { details: { name: 'Pilot', order: 'A', visible: true } },
        'episode-two-branch': { details: { name: 'Episode Two', order: 'B', visible: true } },
      },
    },
    checkpoints: [
      {
        filename: 'native-pilot-checkpoint',
        branchId: 'pilot-branch',
        lines: [
          ['wd-e2e-1', 'Slugline', 'INT. WRITERDUET ROOM - DAY'],
          ['wd-e2e-2', 'Action', 'Two scripts wait on the screen.'],
          ['wd-e2e-3', 'EditDialogName', 'MAYA'],
          ['wd-e2e-4', 'EditDialogContent', 'Bring them both in.'],
        ],
      },
      {
        filename: 'native-episode-two-checkpoint',
        branchId: 'episode-two-branch',
        lines: [
          ['wd-e2e-5', 'Slugline', 'EXT. WRITERDUET STREET - NIGHT'],
          ['wd-e2e-6', 'Action', 'The second story begins.'],
        ],
      },
    ],
  };
  const archiveBase64 = await page.evaluate(async archive => {
    if (!_ensureDocxEngine() || !docx?.JSZip) throw new Error('WriterDuet archive support is unavailable');
    const zip = new docx.JSZip();
    zip.file('script.json', JSON.stringify(archive.metadata));
    archive.checkpoints.forEach((checkpoint, checkpointIndex) => {
      const data = {};
      checkpoint.lines.forEach(([id, type, text], lineIndex) => {
        data[id] = {
          type,
          cache: { t: text, l: 1700000000000 + checkpointIndex * 100 + lineIndex },
        };
      });
      zip.file(checkpoint.filename, JSON.stringify({
        checkpoint: {
          data,
          dataStoreCheckpointIds: {
            checkpoint: {
              checkpointPath: `duet/test/b/${checkpoint.branchId}/checkpoints/users/test/checkpoint.json`,
            },
          },
        },
        setIds: { '.set_id': '-' },
      }));
    });
    return zip.generateAsync({ type: 'base64', compression: 'DEFLATE' });
  }, writerDuetArchive);

  await skript.switchRibbon('import');
  const chooserPromise = page.waitForEvent('filechooser');
  await page.getByTestId('import-writerduet').click();
  const chooser = await chooserPromise;
  await chooser.setFiles({
    name: 'writerduet-e2e-series.wdz',
    mimeType: 'application/zip',
    buffer: Buffer.from(archiveBase64, 'base64'),
  });

  await expect(page.locator('#tabs-container .tab-title')).toHaveText(['Pilot', 'Episode Two']);
  await expect(page.locator('.script-panel:not(.active) .script-line')).toHaveText([
    'INT. WRITERDUET ROOM - DAY',
    'Two scripts wait on the screen.',
    'MAYA',
    'Bring them both in.',
  ]);
  await expect(page.locator('.script-panel.active .script-line')).toHaveText([
    'EXT. WRITERDUET STREET - NIGHT',
    'The second story begins.',
  ]);
  await expect.poll(() => page.evaluate(() => tabs.map(tab => tab.collectionTitle))).toEqual([
    'WriterDuet E2E Series',
    'WriterDuet E2E Series',
  ]);
  await expect.poll(() => page.evaluate(() => tabs.map(tab => tab.importProfile?.source))).toEqual([
    'writerduet',
    'writerduet',
  ]);
  await expect.poll(() => page.evaluate(() => tabs.map(tab => getCoverData(tab.id)?.author))).toEqual([
    'E2E Writer',
    'E2E Writer',
  ]);
});

test('a user can export Word, Final Draft, and invoke PDF export', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'desktop-chromium', 'Downloads are covered once on desktop');
  const fixture = path.join(HERE, 'fixtures', 'loaded.script');
  await skript.loadLocalFile(fixture);
  await skript.switchRibbon('export');

  const wordPromise = page.waitForEvent('download');
  await page.getByTestId('export-word').click();
  const wordDownload = await wordPromise;
  expect(wordDownload.suggestedFilename()).toBe('E2E_Loaded_Script.docx');
  const wordBytes = await fs.readFile(await wordDownload.path());
  expect(wordBytes.subarray(0, 2).toString('ascii')).toBe('PK');
  expect(wordBytes.length).toBeGreaterThan(1000);

  const fdxPromise = page.waitForEvent('download');
  await page.getByTestId('export-fdx').click();
  const fdxDownload = await fdxPromise;
  expect(fdxDownload.suggestedFilename()).toMatch(/\.fdx$/i);
  const fdx = await fs.readFile(await fdxDownload.path(), 'utf8');
  expect(fdx).toContain('<FinalDraft');
  expect(fdx).toContain('INT. AUTOMATION LAB - DAY');

  await page.evaluate(() => {
    const exportTabId = activeTabId;
    createTab('DO NOT EXPORT');
    const otherLine = getLinesContainer(activeTabId)?.querySelector('.script-line');
    if (otherLine) otherLine.textContent = 'INT. OTHER PROJECT - NIGHT';
    activateTab(exportTabId);
  });
  let pdfPayload;
  await page.route('**/api/export-pdf', async route => {
    pdfPayload = route.request().postDataJSON();
    await route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ ok: true, path: 'E2E_Loaded_Script.pdf' }),
    });
  });
  await page.getByTestId('export-pdf').click();
  await expect(page.locator('#pdf-export-modal')).toBeVisible();
  await page.getByTestId('confirm-export-pdf').click();
  await expect.poll(() => pdfPayload?.title).toBe('E2E Loaded Script');
  expect(pdfPayload.lines.map(line => line.text)).toContain('INT. AUTOMATION LAB - DAY');
  expect(pdfPayload.lines.map(line => line.text)).not.toContain('INT. OTHER PROJECT - NIGHT');
  expect(pdfPayload.layoutVersion).toBe(1);
  expect(pdfPayload.layout.map(line => line.text)).toContain('INT. AUTOMATION LAB - DAY');
  expect(pdfPayload.layout.map(line => line.text)).not.toContain('INT. OTHER PROJECT - NIGHT');
  expect(await page.evaluate(() => window.__skriptPrintCalls)).toBe(0);
});
