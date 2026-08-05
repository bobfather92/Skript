import { test, expect } from './support/fixtures.js';


test('storyboard studio provides linked panes, views, filters, inspector sync and responsive navigation', async ({ page, skript }) => {
  await page.evaluate(() => {
    const sceneLine = document.querySelector('.script-panel.active .script-line[data-type="scene"]');
    sceneLine.textContent = 'EXT. CITY SQUARE - DAY';
    const sceneLineId = ensureScriptLineId(sceneLine);
    SL.setData({
      shots: [{
        id:'sl901', type:'shot', sceneIdx:1, sceneLineId, lineId:sceneLineId,
        size:'Wide Shot', movement:'Static', angle:'Eye Level', lens:'35mm',
        location:'City Square', duration:'7', desc:'Establish the square',
        tasks:[], comments:[], flags:[], notes:'', autoManaged:false
      }],
      media:[], settings:{ visibleCols:['num','scene','storyboard','size','desc','actions'], suppressedAutoKeys:[] }
    });
    const frames = [makeStoryboardFrame(0),makeStoryboardFrame(1),makeStoryboardFrame(2)];
    Object.assign(frames[0], { sceneLineId, shotId:'sl901', label:'City Establishing', status:'Review', tags:['city','exterior'], location:'City Square' });
    Object.assign(frames[1], { sceneLineId, label:'Crowd detail', status:'Draft' });
    Object.assign(frames[2], { label:'Loose reference', status:'Draft' });
    const board = { id:91901, name:'Studio test', orientation:'portrait', cols:3, captions:true, aspectRatio:'16:9', status:'Draft', description:'Production board', frames };
    sb.boards = [board];
    sb.activeBoardId = board.id;
    sb.activeFrameId = frames[0].id;
    sb.selectedFrameIds = new Set([frames[0].id]);
    sb.studioView = 'grid';
    sb.studioScene = 'all';
    sb.studioSearch = '';
    sb.studioFilters = {status:'',tag:'',character:'',location:'',shotType:''};
    sb.mobilePane = 'board';
    showStoryboardArea();
    renderStoryboard(board);
  });

  const compactAtStart = (await page.viewportSize()).width <= 900;
  await expect(page.locator('.sb-studio')).toBeVisible();
  await expect(page.locator('.sb-studio-scenes')).toHaveCount(0);
  await expect(page.locator('#sb-storyboard-scenes-nav')).toBeVisible();
  if (compactAtStart) {
    await expect(page.locator('.sb-studio-inspector')).toBeHidden();
  } else {
    await expect(page.locator('.sb-studio-inspector')).toBeVisible();
  }
  await expect(page.locator('#sb-storyboard-scenes-nav .sb-storyboard-scene-item', { hasText:'Unlinked frames' }).locator('.sb-storyboard-scene-count')).toHaveText('1');
  await expect(page.locator('.sb-studio-group')).toHaveCount(2);
  await expect(page.locator('.sb-frame')).toHaveCount(3);
  await expect(page.locator('.sb-frame-link-controls')).toHaveCount(0);
  await expect(page.locator('.sb-frame-link-summary')).toHaveCount(0);
  await expect(page.locator('.sb-frame-metadata .sb-meta-pill[title="Frame label"]')).toHaveCount(0);
  await expect(page.locator('#elements-rg')).toBeHidden();
  await expect(page.locator('#acts-rg')).toBeHidden();
  await expect(page.locator('#sb-zoom-bar')).toBeHidden();
  await expect(page.locator('.sb-studio-zoom')).toBeVisible();
  await expect(page.locator('#sb-toolbar .sb-board-menu-btn')).toBeVisible();

  await page.locator('.sb-studio-view-switch [title="List view"]').click();
  await expect(page.locator('.sb-studio-grid.list')).toHaveCount(2);
  await page.locator('.sb-studio-view-switch [title="Compact view"]').click();
  await expect(page.locator('.sb-studio-grid.compact')).toHaveCount(2);

  await page.evaluate(() => storyboardStudioSetFilter('status','Review'));
  await expect(page.locator('.sb-frame')).toHaveCount(1);
  await page.evaluate(() => storyboardStudioClearFilters());

  if (compactAtStart) await page.evaluate(() => storyboardStudioTogglePane('inspector'));
  await expect(page.locator('.sb-studio-inspector').getByLabel('Label')).toHaveValue('City Establishing');
  await page.locator('.sb-studio-inspector').getByLabel('Shot size').selectOption('Close-Up');
  const synced = await page.evaluate(() => ({
    frame: sb.boards[0].frames[0].shotSize,
    shot: SL.getData().shots.find(item => item.id === 'sl901').size
  }));
  expect(synced).toEqual({ frame:'Close-Up', shot:'Close-Up' });
  if (compactAtStart) await page.evaluate(() => storyboardStudioClosePane('inspector'));

  await page.getByRole('button', { name:'Timeline', exact:true }).click();
  await expect(page.locator('.sb-dock-strip-card')).toHaveCount(3);

  await page.setViewportSize({ width:800, height:600 });
  await page.evaluate(() => { sb.mobilePane = 'board'; renderStoryboard(); });
  await expect(page.locator('.sb-studio-main')).toBeVisible();
  await expect(page.locator('#sb-storyboard-scenes-nav')).toBeVisible();
  await page.evaluate(() => storyboardStudioTogglePane('inspector'));
  await expect(page.locator('.sb-studio')).toHaveAttribute('data-mobile-pane','inspector');
  await expect(page.locator('.sb-studio-inspector')).toBeVisible();
  await expect(page.locator('.sb-studio-main')).toBeHidden();
});
