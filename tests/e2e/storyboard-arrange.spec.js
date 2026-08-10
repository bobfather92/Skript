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
  await expect(cards.nth(0).locator('.sb-frame-drag-handle')).toHaveAttribute('aria-label', 'Move frame 1');
  await expect(cards.nth(0).locator('.sb-frame-drag-handle svg')).toBeVisible();
  await expect(cards.nth(0).locator('.sb-frame-num-badge')).toHaveText('01');
  await cards.nth(0).locator('.sb-frame-select').click();
  await cards.nth(1).locator('.sb-frame-select').click();
  await expect(page.locator('.sb-frame-selected')).toHaveCount(2);
  await expect(page.locator('#sb-ribbon-selection-count')).toHaveText('(2 selected)');
  await cards.nth(2).locator('.sb-frame-select').click();
  await expect(page.locator('#sb-ribbon-selection-count')).toHaveText('(3 selected)');
  await cards.nth(2).locator('.sb-frame-select').click();
  await expect(page.locator('#sb-ribbon-selection-count')).toHaveText('(2 selected)');

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

test('dragging a storyboard frame opens a live animated insertion slot and reorders the sequence', async ({ page, skript }) => {
  const result = await page.evaluate(async () => {
    const board = {
      id: 91002,
      name: 'Animated frame movement',
      orientation: 'portrait',
      cols: 3,
      captions: true,
      currentPage: 0,
      frames: Array.from({ length: 3 }, (_, index) => ({
        ...makeStoryboardFrame(index),
        caption: `Sequence ${index + 1}`,
      })),
    };
    sb.boards = [board];
    sb.activeBoardId = board.id;
    sb.selectedFrameIds.clear();
    showStoryboardArea();
    renderStoryboard(board);

    const source = document.querySelectorAll('.sb-frame')[0];
    const target = document.querySelectorAll('.sb-frame')[1];
    const handle = source.querySelector('.sb-frame-drag-handle');
    const dataTransfer = new DataTransfer();
    sbFrameDragStart({ currentTarget:handle, dataTransfer },board.id,source.dataset.frameId);
    await new Promise(resolve => setTimeout(resolve,30));
    const targetRect = target.getBoundingClientRect();
    const event = {
      currentTarget:target,
      dataTransfer,
      clientX:targetRect.right - 2,
      clientY:targetRect.top + targetRect.height / 2,
      preventDefault() {},
    };
    sbFrameDragOver(event);
    const placeholder = document.querySelector('.sb-frame-drop-slot');
    const liveState = {
      placeholderVisible:Boolean(placeholder),
      placeholderAfterTarget:placeholder?.previousElementSibling === target,
      sourceHidden:source.classList.contains('sb-frame-drag-source'),
      label:placeholder?.textContent.trim(),
      reflowAnimations:document.getAnimations().filter(animation => animation.playState === 'running').length,
    };
    sbFrameDrop(event,board.id,target.dataset.frameId);
    return {
      ...liveState,
      captions:board.frames.map(frame => frame.caption),
      placeholderRemoved:!document.querySelector('.sb-frame-drop-slot'),
      renumbered:Array.from(document.querySelectorAll('.sb-frame-num-badge')).map(node => node.textContent),
    };
  });

  expect(result).toMatchObject({
    placeholderVisible:true,
    placeholderAfterTarget:true,
    sourceHidden:true,
    label:'Move frame',
    captions:['Sequence 2', 'Sequence 1', 'Sequence 3'],
    placeholderRemoved:true,
    renumbered:['01', '02', '03'],
  });
  expect(result.reflowAnimations).toBeGreaterThan(0);
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
