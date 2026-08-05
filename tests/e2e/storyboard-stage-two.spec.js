import { test, expect } from './support/fixtures.js';

test('new storyboard uses a guided wizard matching the New Script flow', async ({ page, skript }) => {
  await page.evaluate(() => {
    sb.boards = [];
    sb.activeBoardId = null;
    sb.template = 'film';
    sb.aspectRatio = '16:9';
    sb.orientation = 'portrait';
    sb.cols = 2;
    sb.captions = true;
    sb.frameCount = 6;
    sb.actionSafe = false;
    sb.titleSafe = false;
    newStoryboard();
  });

  const modal = page.locator('#sb-setup-modal');
  await expect(modal).toHaveClass(/open/);
  await expect(page.locator('#sb-wiz-header .wiz-step')).toHaveCount(4);
  await expect(page.locator('#sb-wiz-title-line')).toHaveText('Choose a storyboard template');
  await expect(page.locator('.sb-wiz-template-grid .wiz-type-card')).toHaveCount(7);

  await page.getByRole('button', { name: /Feature Film Scope/ }).click();
  await page.locator('#sb-wiz-next').click();
  await expect(page.locator('#sb-wiz-title-line')).toHaveText('Name and frame your board');
  await page.locator('#sb-wiz-name').fill('Opening Chase');
  await page.getByRole('button', { name: /^1:1 Square$/ }).click();
  await page.locator('#sb-wiz-next').click();

  await expect(page.locator('#sb-wiz-title-line')).toHaveText('Configure the page layout');
  await page.getByRole('button', { name: /Landscape Wider presentation/ }).click();
  await page.getByRole('button', { name: /Two frames Larger artwork/ }).click();
  await page.getByRole('button', { name: /Hide captions Artwork/ }).click();
  await page.getByRole('button', { name: /12 frames A complete scene/ }).click();
  await page.getByText('Title-safe overlay', { exact: true }).click();
  await page.locator('#sb-wiz-next').click();

  await expect(page.locator('#sb-wiz-title-line')).toHaveText('Ready to create?');
  await expect(page.locator('#sb-wiz-body')).toContainText('Opening Chase');
  await expect(page.locator('#sb-wiz-body')).toContainText('1:1 · 12 starting frames');
  await expect(page.locator('#sb-wiz-body')).toContainText('Landscape · 2 per row · no captions');

  const box = await page.locator('#sb-wiz-box').boundingBox();
  const viewport = page.viewportSize();
  expect(box.width).toBeLessThanOrEqual(viewport.width);
  expect(box.height).toBeLessThanOrEqual(viewport.height);

  await page.locator('#sb-wiz-next').click();
  await expect(modal).not.toHaveClass(/open/);
  const board = await page.evaluate(() => sb.boards[0]);
  expect(board).toMatchObject({
    name: 'Opening Chase', aspectRatio: '1:1', orientation: 'landscape',
    cols: 2, captions: false, titleSafe: true,
  });
  expect(board.frames).toHaveLength(12);
});

test('storyboard settings and rich frame information persist and duplicate safely', async ({ page, skript }) => {
  const result = await page.evaluate(() => {
    const board = {
      id: 93001,
      name: 'Legacy board',
      orientation: 'portrait',
      cols: 3,
      captions: true,
      currentPage: 0,
      frames: [{ imageData: null, caption: 'A legacy frame', layers: null }],
    };
    sb.boards = [board];
    sb.activeBoardId = board.id;
    sb.history = [];
    sb.redoHistory = [];
    ensureStoryboardFrameIds(board);
    renderStoryboard(board);

    openStoryboardSettings();
    document.getElementById('sbs-name').value = 'Night Sequence';
    document.getElementById('sbs-description').value = 'Exterior pickup sequence';
    document.getElementById('sbs-status').value = 'Review';
    document.getElementById('sbs-template').value = 'custom';
    document.getElementById('sbs-aspect').value = 'custom';
    document.getElementById('sbs-custom-w').value = '5';
    document.getElementById('sbs-custom-h').value = '4';
    document.getElementById('sbs-orientation').value = 'landscape';
    document.getElementById('sbs-cols').value = '2';
    document.getElementById('sbs-captions').checked = false;
    document.getElementById('sbs-action-safe').checked = true;
    document.getElementById('sbs-title-safe').checked = true;
    saveStoryboardSettings();

    openStoryboardFrameInfo(board.id, 0);
    document.getElementById('sbfi-label').value = 'Establishing shot';
    document.getElementById('sbfi-shot-number').value = '12A';
    document.getElementById('sbfi-duration').value = '00:00:05:12';
    document.getElementById('sbfi-status').value = 'Approved';
    document.getElementById('sbfi-tags').value = 'night, exterior, night';
    document.getElementById('sbfi-action').value = 'Car enters frame';
    document.getElementById('sbfi-dialogue').value = 'Engine and rain';
    document.getElementById('sbfi-camera').value = '24mm slow push';
    document.getElementById('sbfi-lighting').value = 'Wet-down reflections';
    document.getElementById('sbfi-transition').value = 'Dissolve to interior';
    addStoryboardCustomField({ label: 'VFX', value: 'Remove safety rig' });
    saveStoryboardFrameInfo();

    const originalFrameId = board.frames[0].id;
    duplicateStoryboardBoard();
    const duplicate = sb.boards[1];
    const stored = JSON.parse(localStorage.getItem('sf-storyboard'));
    return {
      board: stored.boards[0],
      frame: stored.boards[0].frames[0],
      duplicateName: duplicate.name,
      duplicateFrameId: duplicate.frames[0].id,
      originalFrameId,
      cards: document.querySelectorAll('.sb-frame').length,
      aspectStyle: document.querySelector('.sb-canvas-wrap')?.style.getPropertyValue('--sb-frame-aspect'),
      safeGuides: document.querySelectorAll('.sb-safe-overlay > div').length,
    };
  });

  expect(result.board).toMatchObject({
    name: 'Night Sequence', description: 'Exterior pickup sequence', status: 'Review',
    aspectRatio: 'custom', customAspectW: 5, customAspectH: 4,
    orientation: 'landscape', cols: 2, captions: false,
    actionSafe: true, titleSafe: true,
  });
  expect(result.frame).toMatchObject({
    label: 'Establishing shot', shotNumber: '12A', duration: '00:00:05:12', status: 'Approved',
    actionNotes: 'Car enters frame', dialogueNotes: 'Engine and rain', cameraNotes: '24mm slow push',
    lightingNotes: 'Wet-down reflections', transitionNotes: 'Dissolve to interior',
    tags: ['night', 'exterior'],
  });
  expect(result.frame.customFields).toEqual(expect.arrayContaining([
    expect.objectContaining({ label: 'VFX', value: 'Remove safety rig' }),
  ]));
  expect(result.duplicateName).toBe('Night Sequence Copy');
  expect(result.duplicateFrameId).not.toBe(result.originalFrameId);
  expect(result.cards).toBe(1);
  expect(Number(result.aspectStyle)).toBeCloseTo(1.25);
  expect(result.safeGuides).toBe(2);
});

test('image transforms, object locks, layer tools and project media survive frame save', async ({ page, skript }) => {
  const result = await page.evaluate(async () => {
    const board = {
      id: 94001, name: 'Media board', orientation: 'portrait', cols: 2, captions: true,
      aspectRatio: '9:16', customAspectW: 9, customAspectH: 16,
      currentPage: 0, frames: [makeStoryboardFrame(0)],
    };
    sb.boards = [board];
    sb.activeBoardId = board.id;
    sb.mediaLibrary = [];
    openFrameEditor(0, board.id);

    const makeImageFile = (name, colour) => new File([
      `<svg xmlns="http://www.w3.org/2000/svg" width="400" height="200"><rect width="400" height="200" fill="${colour}"/></svg>`,
    ], name, { type: 'image/svg+xml' });
    await feImportImageFiles([
      makeImageFile('location-a.svg', '#77aadd'),
      makeImageFile('location-b.svg', '#dd9977'),
    ]);
    const ref = feGetSelectedRefs().find(candidate => candidate.obj.id === fe.primaryObjectId);
    const originalActiveId = ref.obj.id;
    feSetSelectedImageMode('crop');
    feNudgeCrop(-0.6, 0.2);
    feRotateSelected(90);
    feFlipSelected('x');
    feBeginObjectOpacityChange();
    feSetSelectedObjectOpacity(55);
    feEndObjectOpacityChange();

    feToggleSelectedObjectLock();
    const lockedHit = feFindTopObjectAt(ref.obj.x + 2, ref.obj.y + 2);
    const editableWhileLocked = feGetEditableSelectedRefs().length;
    feToggleSelectedObjectLock();

    const layersBeforeLockedDelete = fe.layers.length;
    feToggleActiveLayerLock();
    feDeleteActiveLayer();
    const layersAfterLockedDelete = fe.layers.length;
    feToggleActiveLayerLock();
    feDuplicateActiveLayer();
    const duplicateId = fe.layers[fe.activeLayerIdx].objects[0].id;
    feRenameLayer(fe.activeLayerIdx);
    document.getElementById('fe-layer-rename-input').value = 'Location Plate Copy';
    saveLayerRename();
    feToggleAspectLock();
    const aspectLockAfterToggle = fe.aspectLock;

    saveFrameEditor();
    const saved = board.frames[0];
    const source = saved.layers.find(layer => layer.name === 'Image: location-b')?.objects[0];
    const duplicate = saved.layers.find(layer => layer.name === 'Location Plate Copy');
    const stored = JSON.parse(localStorage.getItem('sf-storyboard'));
    return {
      canvas: [fe.canvasW, fe.canvasH],
      mediaCount: stored.mediaLibrary.length,
      mediaFormats: stored.mediaLibrary.map(item => item.src.split(';')[0]),
      source,
      duplicateName: duplicate?.name,
      duplicateId,
      sourceId: originalActiveId,
      layersBeforeLockedDelete,
      layersAfterLockedDelete,
      lockedHit: !!lockedHit,
      editableWhileLocked,
      aspectLockAfterToggle,
      storedLayerLocks: stored.boards[0].frames[0].layers.map(layer => !!layer.locked),
    };
  });

  expect(result.canvas).toEqual([608, 1080]);
  expect(result.mediaCount).toBe(2);
  expect(result.mediaFormats).toEqual(['data:image/webp', 'data:image/webp']);
  expect(result.source).toMatchObject({
    imageMode: 'crop', cropX: 0, cropY: 0.7,
    rotation: 90, flipX: true, opacity: 0.55, locked: false,
  });
  expect(result.duplicateName).toBe('Location Plate Copy');
  expect(result.duplicateId).not.toBe(result.sourceId);
  expect(result.layersAfterLockedDelete).toBe(result.layersBeforeLockedDelete);
  expect(result.lockedHit).toBe(true);
  expect(result.editableWhileLocked).toBe(0);
  expect(result.aspectLockAfterToggle).toBe(false);
  expect(result.storedLayerLocks.every(lock => lock === false)).toBe(true);
});
