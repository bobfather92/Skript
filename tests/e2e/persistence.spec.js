import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { test, expect } from './support/fixtures.js';


const HERE = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(HERE, '..', '..');
const savedPath = path.join(ROOT, 'tmp', 'e2e-data', 'scripts', 'UNTITLED SCRIPT.script');

test('a user can save through the desktop service and reopen locally', async ({ page, skript }) => {
  await fs.rm(savedPath, { force: true });
  await skript.activeLines.nth(0).fill('INT. SAVED LAB - NIGHT');

  await page.getByTestId('save-script').click();
  await expect(page.locator('#sf-toast')).toContainText('Saved');
  await expect.poll(async () => {
    try { return (await fs.stat(savedPath)).size; } catch (_) { return 0; }
  }).toBeGreaterThan(50);

  const saved = JSON.parse(await fs.readFile(savedPath, 'utf8'));
  expect(saved.schema).toBe('com.skript.project');
  expect(saved.version).toBe(6);
  expect(saved.projectId).toMatch(/^project-/);
  expect(saved.integrity).toMatchObject({ algorithm: 'fnv1a32' });
  expect(saved.title).toBe('UNTITLED SCRIPT');
  expect(saved.lines[0]).toMatchObject({ type: 'scene', text: 'INT. SAVED LAB - NIGHT' });
  expect(saved.lines[0].lineId).toMatch(/^line-/);

  await skript.loadLocalFile(savedPath);
  await expect(page.locator('.tab.active .tab-title')).toHaveText('UNTITLED SCRIPT');
  await expect(skript.activeLines.nth(0)).toHaveText('INT. SAVED LAB - NIGHT');
});

test('legacy projects migrate without dropping documents or revision marks', async ({ page, skript }) => {
  await page.evaluate(() => importTabFromData({
    version: 1,
    title: 'Legacy Draft',
    subtitle: 'Based on an earlier treatment',
    notes: ['Keep this note'],
    shotList: { scene1: { shots: [{ id: 1, type: 'Wide' }] } },
    breakdown: { scene1: { cats: { props: ['Key'] } } },
    lines: [
      { type: 'scene', text: 'INT. ARCHIVE - DAY', lineId: 'duplicate', rev: 'change' },
      { type: 'unknown-old-type', text: 'Dust hangs in the air.', lineId: 'duplicate' },
    ],
  }));
  const migrated = await page.evaluate(() => serializeCurrentProject());

  expect(migrated.version).toBe(6);
  expect(migrated.cover.basedOn).toBe('Based on an earlier treatment');
  expect(migrated.notes).toEqual(['Keep this note']);
  expect(migrated.shotList.legacy.scene1.shots).toHaveLength(1);
  expect(migrated.breakdown.scene1.cats.props).toEqual(['Key']);
  expect(migrated.lines[0].rev).toBe('change');
  expect(migrated.lines[1].type).toBe('action');
  expect(migrated.lines[0].lineId).not.toBe(migrated.lines[1].lineId);
});

test('recovery captures every open project and detects same-length edits', async ({ page, skript }) => {
  await skript.activeLines.first().fill('INT. FIRST ROOM - DAY');
  await page.evaluate(() => createTabFromData({
    version: 4,
    title: 'Second Project',
    format: 'tv',
    cover: { title: 'Second Project' },
    lines: [{ type: 'scene', text: 'INT. SECOND ROOM - NIGHT', lineId: 'second-scene' }],
  }));

  const before = await page.evaluate(() => {
    const snapshot = serializeRecoveryWorkspace();
    return { snapshot, fingerprint: recoveryFingerprint(snapshot) };
  });
  expect(before.snapshot.projects).toHaveLength(2);
  expect(before.snapshot.projects.map(project => project.title)).toEqual(['UNTITLED SCRIPT', 'Second Project']);

  await skript.activeLines.first().fill('INT. SECOND HALL - NIGHT');
  const after = await page.evaluate(() => {
    const snapshot = serializeRecoveryWorkspace();
    return recoveryFingerprint(snapshot);
  });
  expect(after).not.toBe(before.fingerprint);
});

test('a user can open an existing Skript document with the local picker', async ({ page, skript }) => {
  const fixture = path.join(HERE, 'fixtures', 'loaded.script');
  await skript.loadLocalFile(fixture);
  await expect(page.locator('.tab.active .tab-title')).toHaveText('E2E Loaded Script');
  await expect(skript.activeLines).toHaveCount(4);
  await expect(skript.activeLines).toHaveText([
    'INT. AUTOMATION LAB - DAY',
    'A status light turns green.',
    'MAYA',
    'The test is running.',
  ]);
});
