import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { test, expect } from './support/fixtures.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(HERE, '..', '..');
const savedPath = path.join(ROOT, 'tmp', 'e2e-data', 'scripts', 'MULTI SCRIPT E2E.script');

test('multi-script projects manage documents and save as one reopenable project', async ({ page, skript }) => {
  await fs.rm(savedPath, { force: true });
  await skript.activeLines.first().fill('INT. PILOT ROOM - DAY');
  await page.evaluate(() => {
    localStorage.setItem('sf-storyboard', JSON.stringify({
      version: 4,
      boards: [{ id: 'shared-board', name: 'Shared Board', frames: [] }],
      activeBoardId: 'shared-board',
      mediaLibrary: [{ id: 'shared-media', name: 'Reference.jpg' }],
    }));
    addScriptToActiveProject('EPISODE TWO');
  });
  await skript.activeLines.first().fill('EXT. SECOND STREET - NIGHT');
  await page.evaluate(() => renameActiveProject('MULTI SCRIPT E2E'));

  await expect(page.locator('#project-scripts-navigator .project-script-row')).toHaveCount(2);
  await expect(page.locator('#project-scripts-navigator .project-script-open')).toHaveText([
    /UNTITLED SCRIPT/,
    /EPISODE TWO/,
  ]);

  await page.evaluate(() => duplicateProjectScript(activeTabId));
  await expect(page.locator('#project-scripts-navigator .project-script-row')).toHaveCount(3);
  await page.evaluate(() => {
    const copy = tabs.find(tab => tab.title === 'EPISODE TWO COPY');
    renameProjectScript(copy.id, 'EPISODE THREE');
    moveProjectScript(copy.id, -1);
  });
  await expect(page.locator('#project-scripts-navigator .project-script-open')).toHaveText([
    /UNTITLED SCRIPT/,
    /EPISODE THREE/,
    /EPISODE TWO/,
  ]);

  await page.evaluate(() => {
    const middle = tabs.find(tab => tab.title === 'EPISODE THREE');
    removeProjectScript(middle.id, true);
  });
  await expect(page.locator('#project-scripts-navigator .project-script-row')).toHaveCount(2);

  const inMemory = await page.evaluate(() => {
    const active = tabs.find(tab => tab.id === activeTabId);
    const project = buildProjectCollectionData(active.collectionId);
    const recoveryWorkspace = serializeRecoveryWorkspace();
    return { project, recoveryWorkspace };
  });
  expect(inMemory.project).toMatchObject({
    schema: 'com.skript.project-collection',
    version: 2,
    title: 'MULTI SCRIPT E2E',
  });
  expect(inMemory.project.scripts.map(script => script.title)).toEqual(['UNTITLED SCRIPT', 'EPISODE TWO']);
  expect(inMemory.project.shared.storyboard.boards[0].id).toBe('shared-board');
  expect(inMemory.project.shared.storyboard.mediaLibrary[0].id).toBe('shared-media');
  expect(inMemory.project.scripts.every(script => !Object.hasOwn(script, 'storyboard'))).toBe(true);
  expect(inMemory.recoveryWorkspace.projects).toHaveLength(1);
  expect(inMemory.recoveryWorkspace.projects[0].scripts).toHaveLength(2);

  await page.getByTestId('save-script').click();
  await expect(page.locator('#sf-toast')).toContainText('Saved');
  await expect.poll(async () => {
    try { return (await fs.stat(savedPath)).size; } catch (_) { return 0; }
  }).toBeGreaterThan(100);
  const saved = JSON.parse(await fs.readFile(savedPath, 'utf8'));
  expect(saved.schema).toBe('com.skript.project-collection');
  expect(saved.scripts).toHaveLength(2);

  await page.evaluate(() => {
    tabs.forEach(tab => {
      document.querySelector(`.tab[data-id="${tab.id}"]`)?.remove();
      document.querySelector(`.script-panel[data-tab-id="${tab.id}"]`)?.remove();
      document.querySelector(`.cover-view[data-cover-id="${tab.id}"]`)?.remove();
    });
    tabs = [];
    activeTabId = null;
    projectCollections.clear();
    createTab('UNTITLED SCRIPT');
  });
  await page.locator('#file-input').setInputFiles({
    name: 'MULTI SCRIPT E2E.script',
    mimeType: 'application/json',
    buffer: Buffer.from(JSON.stringify(saved)),
  });
  await expect(page.locator('#tabs-container .tab-title')).toHaveText(['UNTITLED SCRIPT', 'EPISODE TWO']);
  await expect(page.locator('#project-scripts-navigator .project-script-row')).toHaveCount(2);
  const reopened = await page.evaluate(() => {
    const active = tabs.find(tab => tab.id === activeTabId);
    return {
      collectionTitle: projectCollections.get(active.collectionId)?.title,
      storyboard: JSON.parse(localStorage.getItem('sf-storyboard')),
    };
  });
  expect(reopened.collectionTitle).toBe('MULTI SCRIPT E2E');
  expect(reopened.storyboard.mediaLibrary[0].id).toBe('shared-media');
});

test('recovery restores a multi-script project as one unsaved collection', async ({ page, skript }) => {
  await skript.activeLines.first().fill('INT. RECOVERY ONE - DAY');
  await page.evaluate(() => addScriptToActiveProject('RECOVERY TWO'));
  await skript.activeLines.first().fill('EXT. RECOVERY TWO - NIGHT');

  const result = await page.evaluate(() => {
    const workspace = serializeRecoveryWorkspace();
    const originalCollectionId = tabs.find(tab => tab.id === activeTabId).collectionId;
    const count = restoreRecoveryPayload(workspace);
    const recoveredTabs = tabs.filter(tab => tab.collectionId && tab.collectionId !== originalCollectionId);
    return {
      count,
      titles: recoveredTabs.map(tab => tab.title),
      dirty: recoveredTabs.map(tab => tab.dirty),
      paths: recoveredTabs.map(tab => tab.filePath),
      oneCollection: new Set(recoveredTabs.map(tab => tab.collectionId)).size,
    };
  });
  expect(result.count).toBe(2);
  expect(result.titles).toEqual(['UNTITLED SCRIPT', 'RECOVERY TWO']);
  expect(result.dirty).toEqual([true, true]);
  expect(result.paths).toEqual(['', '']);
  expect(result.oneCollection).toBe(1);
});

test('Save As and autosave each write the complete collection once', async ({ page, skript }) => {
  await skript.activeLines.first().fill('INT. SAVE AS ONE - DAY');
  await page.evaluate(() => addScriptToActiveProject('SAVE AS TWO'));
  await skript.activeLines.first().fill('EXT. SAVE AS TWO - NIGHT');

  const result = await page.evaluate(async () => {
    const originalFetch = sfApiFetch;
    const requests = [];
    sfApiFetch = async (endpoint, options = {}) => {
      if (endpoint === '/api/save' || endpoint === '/api/save-auto') {
        const body = JSON.parse(options.body);
        requests.push({ endpoint, body, project: JSON.parse(body.content) });
        return new Response(JSON.stringify({ ok: true, path: 'C:\\Projects\\Series.script' }), {
          status: 200,
          headers: { 'Content-Type': 'application/json' },
        });
      }
      return originalFetch(endpoint, options);
    };
    try {
      window._saveWithDialog = true;
      const saveAsResult = await saveScript(false);
      const firstTab = tabs.find(tab => tab.collectionId);
      activateTab(firstTab.id);
      markUnsaved();
      const autosaveResult = await autosaveAllDirtyProjects();
      return {
        saveAsResult,
        autosaveResult,
        requests,
        paths: tabs.map(tab => tab.filePath),
        dirty: tabs.map(tab => tab.dirty),
      };
    } finally {
      sfApiFetch = originalFetch;
    }
  });

  expect(result.saveAsResult).toBe(true);
  expect(result.autosaveResult).toEqual({ saved: 1, total: 1 });
  expect(result.requests.map(request => request.endpoint)).toEqual(['/api/save', '/api/save-auto']);
  expect(result.requests.every(request => request.project.schema === 'com.skript.project-collection')).toBe(true);
  expect(result.requests.every(request => request.project.scripts.length === 2)).toBe(true);
  expect(result.paths).toEqual(['C:\\Projects\\Series.script', 'C:\\Projects\\Series.script']);
  expect(result.dirty).toEqual([false, false]);
});

test('script rename dialog can be cancelled or confirmed', async ({ page, skript }) => {
  await page.evaluate(() => addScriptToActiveProject('EPISODE TWO'));
  const activeRow = page.locator('#project-scripts-navigator .project-script-row.active');

  await activeRow.getByTitle('Rename script').click();
  await expect(page.locator('#modal')).toHaveClass(/open/);
  await expect(page.locator('#modal-input')).toHaveValue('EPISODE TWO');
  await expect(page.locator('#modal-confirm-btn')).toHaveText('Rename script');
  await page.locator('#modal-input').fill('CANCELLED NAME');
  await page.locator('#modal-cancel-btn').click();
  await expect(page.locator('#modal')).not.toHaveClass(/open/);
  await expect(page.locator('.tab.active .tab-title')).toHaveText('EPISODE TWO');

  await activeRow.getByTitle('Rename script').click();
  await page.locator('#modal-input').fill('EPISODE THREE');
  await page.locator('#modal-confirm-btn').click();
  await expect(page.locator('#modal')).not.toHaveClass(/open/);
  await expect(page.locator('.tab.active .tab-title')).toHaveText('EPISODE THREE');
  await expect(page.locator('#project-scripts-navigator .project-script-row.active .project-script-open')).toContainText('EPISODE THREE');
});

test('Navigator duplicate button copies an empty project script', async ({ page, skript }) => {
  await page.evaluate(() => addScriptToActiveProject('EMPTY EPISODE'));
  await expect(page.locator('#project-scripts-navigator .project-script-row')).toHaveCount(2);

  await page.locator('#project-scripts-navigator .project-script-row.active').getByTitle('Duplicate script').click();

  await expect(page.locator('#project-scripts-navigator .project-script-row')).toHaveCount(3);
  await expect(page.locator('#tabs-container .tab-title')).toHaveText([
    'UNTITLED SCRIPT',
    'EMPTY EPISODE',
    'EMPTY EPISODE COPY',
  ]);
  await expect(page.locator('.tab.active .tab-title')).toHaveText('EMPTY EPISODE COPY');
  await expect(page.locator('#sf-toast')).toContainText('Duplicated');
  expect(await page.evaluate(() => new Set(tabs.map(tab => tab.projectId)).size)).toBe(3);
});

test('project scripts switch from Navigator without a visible tab strip', async ({ page, skript }) => {
  await skript.activeLines.first().fill('INT. FIRST SCRIPT - DAY');
  await page.evaluate(() => addScriptToActiveProject('SECOND SCRIPT'));
  await skript.activeLines.first().fill('EXT. SECOND SCRIPT - NIGHT');

  await expect(page.locator('#tabbar')).toBeHidden();
  await expect(page.locator('#tabbar')).toHaveAttribute('aria-hidden', 'true');
  const rows = page.locator('#project-scripts-navigator .project-script-row');
  await expect(rows).toHaveCount(2);
  await expect(rows.nth(1).locator('.project-script-open')).toHaveAttribute('aria-current', 'page');

  await rows.nth(0).locator('.project-script-open').click();
  await expect(page.locator('.script-panel.active .script-line').first()).toHaveText('INT. FIRST SCRIPT - DAY');
  await expect(page.locator('#project-scripts-navigator .project-script-row').nth(0).locator('.project-script-open')).toHaveAttribute('aria-current', 'page');
  await expect(page.locator('#project-scripts-navigator .project-script-row').nth(1).locator('.project-script-open')).not.toHaveAttribute('aria-current', 'page');
});
