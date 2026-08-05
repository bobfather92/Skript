import { test, expect } from './support/fixtures.js';

test('storyboard cards support multi-select, duplicate, reorder, delete, undo and redo', async ({ page, skript }) => {
  await page.evaluate(() => {
    const board = {
      id: 91001,
      name: 'Card management test',
      orientation: 'portrait',
      cols: 2,
      captions: true,
      currentPage: 0,
      frames: Array.from({ length: 3 }, (_, index) => ({
        ...makeStoryboardFrame(index),
        caption: `Card ${index + 1}`,
      })),
    };
    sb.boards = [board];
    sb.activeBoardId = board.id;
    sb.selectedFrameIds.clear();
    sb.history = [];
    sb.redoHistory = [];
    showStoryboardArea();
    renderStoryboard(board);
  });

  const cards = page.locator('.sb-frame');
  await expect(cards).toHaveCount(3);
  await cards.nth(0).locator('.sb-frame-select').click();
  await cards.nth(1).locator('.sb-frame-select').click({ modifiers: ['Shift'] });
  await expect(page.locator('.sb-frame-selected')).toHaveCount(2);
  await expect(page.locator('.sb-card-menu > summary')).toContainText('Cards (2)');

  await page.evaluate(() => sbDuplicateSelectedFrames());
  await expect(cards).toHaveCount(5);
  await expect(page.locator('.sb-frame-selected')).toHaveCount(2);

  await page.evaluate(() => sbUndo());
  await expect(cards).toHaveCount(3);
  await page.evaluate(() => sbRedo());
  await expect(cards).toHaveCount(5);

  await page.evaluate(() => {
    const board = sb.boards[0];
    sb.selectedFrameIds = new Set([board.frames[1].id, board.frames[2].id]);
    renderStoryboard(board);
    sbMoveSelectedFrames(1);
  });
  const movedCaptions = await page.evaluate(() => sb.boards[0].frames.map(frame => frame.caption));
  expect(movedCaptions).toEqual(['Card 1', 'Card 2', 'Card 2', 'Card 1', 'Card 3']);

  await page.evaluate(() => sbDeleteSelectedFrames());
  await expect(cards).toHaveCount(3);
  await page.evaluate(() => sbUndo());
  await expect(cards).toHaveCount(5);
});

test('frame editor multi-object arrange commands and redo restore exact object state', async ({ page, skript }) => {
  const state = await page.evaluate(() => {
    const objects = [
      { id: 'shape-a', type: 'shape', shapeType: 'rect', x: 100, y: 100, w: 100, h: 80, x1: 100, y1: 100, x2: 200, y2: 180, color: '#111', lineWidth: 2 },
      { id: 'shape-b', type: 'shape', shapeType: 'rect', x: 350, y: 240, w: 140, h: 60, x1: 350, y1: 240, x2: 490, y2: 300, color: '#222', lineWidth: 2 },
      { id: 'shape-c', type: 'shape', shapeType: 'rect', x: 700, y: 420, w: 80, h: 100, x1: 700, y1: 420, x2: 780, y2: 520, color: '#333', lineWidth: 2 },
    ];
    const board = {
      id: 92001, name: 'Arrange test', orientation: 'landscape', cols: 2,
      captions: true, currentPage: 0,
      frames: [{ ...makeStoryboardFrame(0), layers: objects.map((object, index) => ({
        name: `Shape ${index + 1}`, type: 'shape', visible: true, opacity: 1,
        objects: [object], imageData: null,
      })) }],
    };
    sb.boards = [board];
    sb.activeBoardId = board.id;
    openFrameEditor(0, board.id);
    feSetTool('move', document.getElementById('fept-move'));
    feClearObjectSelection();
    const overlay = document.getElementById('fe-canvas');
    const rect = overlay.getBoundingClientRect();
    const point = (x, y) => ({ clientX: rect.left + x * fe.zoom, clientY: rect.top + y * fe.zoom });
    feMouseDown(point(40, 40));
    feMouseMove(point(840, 560));
    feMouseUp(point(840, 560));
    const refs = feGetSelectedRefs();
    const before = refs.map(ref => ref.obj.y);
    feAlignSelection('top');
    const aligned = feGetSelectedRefs().map(ref => ref.obj.y);
    feUndo();
    const undone = feAllObjectRefs(true).map(ref => ref.obj.y);
    feRedo();
    const redone = feAllObjectRefs(true).map(ref => ref.obj.y);
    feDistributeSelection('horizontal');
    const distributedX = feGetSelectedRefs().map(ref => ref.obj.x).sort((a, b) => a - b);
    const bounds = feSelectionBounds(feGetSelectedRefs());
    const snapped = feGetSnappedMoveDelta(bounds, -bounds.x + 5, 0, {});
    return {
      selected: fe.selectedObjectIds.length,
      before, aligned, undone, redone, distributedX, snapped,
      guideCount: fe.smartGuides.length,
      undoCount: fe.history.length,
    };
  });

  expect(state.selected).toBe(3);
  expect(new Set(state.aligned).size).toBe(1);
  expect(state.undone).toEqual(state.before);
  expect(state.redone).toEqual(state.aligned);
  expect(state.distributedX).toEqual([100, 380, 700]);
  expect(state.snapped.dx).toBe(-100);
  expect(state.guideCount).toBeGreaterThan(0);
  expect(state.undoCount).toBeGreaterThan(0);
  await expect(page.locator('#fe-redo-btn')).toBeDisabled();
  await expect(page.locator('.fe-arrange-menu')).toBeVisible();
});
