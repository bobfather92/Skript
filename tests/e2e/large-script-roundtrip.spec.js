import { test, expect } from './support/fixtures.js';


test('300-scene projects use adaptive performance and incremental Navigator updates', async ({ page, skript }) => {
  const creation = await page.evaluate(() => {
    const lines = [];
    for (let scene = 1; scene <= 300; scene += 1) {
      lines.push({ type:'scene', text:`INT. LOCATION ${scene} - DAY`, lineId:`large-scene-${scene}` });
      lines.push({ type:'action', text:`Action for scene ${scene}.`, lineId:`large-action-${scene}` });
      lines.push({ type:'character', text:'DOCTOR', lineId:`large-character-${scene}` });
      lines.push({ type:'dialogue', text:`Dialogue in scene ${scene}.`, lineId:`large-dialogue-${scene}` });
    }
    const started = performance.now();
    createTabFromData({
      version: 6,
      title: 'Large Performance Test',
      format: 'tv',
      cover: { title:'Large Performance Test' },
      lines,
    });
    return { duration: performance.now() - started, activeTabId };
  });

  expect(creation.duration).toBeLessThan(8000);
  await expect(page.locator('html')).toHaveClass(/sf-large-script/);
  await expect(page.locator('html')).toHaveClass(/sf-low-power/);
  await expect(page.locator('html')).toHaveAttribute('data-performance-reason', 'very-large-script');
  await expect(page.locator('#scene-nav-list .sn-item')).toHaveCount(300);

  await page.locator('#scene-nav-list .sn-item').first().evaluate(item => { item.dataset.incrementalProbe = 'kept'; });
  const firstScene = page.locator('.script-panel.active .script-line[data-type="scene"]').first();
  await firstScene.fill('INT. UPDATED LOCATION - NIGHT');
  await expect(page.locator('#scene-nav-list .sn-item').first()).toContainText('UPDATED LOCATION');
  await expect(page.locator('#scene-nav-list .sn-item').first()).toHaveAttribute('data-incremental-probe', 'kept');
  await expect(page.locator('#scene-count-status')).toContainText('300');
});


test('import metadata and Stage Play formatting survive save and PDF export', async ({ page, skript }) => {
  await page.evaluate(() => createTabFromData({
    version: 6,
    source: 'pdf',
    title: 'Round Trip Play',
    format: 'play',
    cover: { title:'Round Trip Play', author:'Test Writer' },
    importProfile: {
      version:1, source:'pdf', sourceLabel:'PDF', detectedFormat:'play',
      selectedFormat:'play', confidence:96, importedAt:'2026-07-15T12:00:00.000Z'
    },
    lines: [
      { type:'act', text:'ACT I', lineId:'rt-act', importMeta:{source:'pdf',detectedType:'act',confidence:97,needsReview:false,reviewed:true} },
      { type:'scene', text:'SCENE 1', lineId:'rt-scene', importMeta:{source:'pdf',detectedType:'scene',confidence:97,needsReview:false,reviewed:true} },
      { type:'stage-direction', text:'Lights rise.', lineId:'rt-direction', importMeta:{source:'pdf',detectedType:'stage-direction',confidence:88,needsReview:false,reviewed:true} },
      { type:'character', text:'HAMLET', lineId:'rt-character' },
      { type:'dialogue', text:'To be.', lineId:'rt-dialogue' },
    ],
  }));

  const direction = page.locator('.script-panel.active .script-line[data-type="stage-direction"]');
  await direction.fill('Lights rise slowly.');
  await expect(direction).toHaveText('Lights rise slowly.');

  const roundTrip = await page.evaluate(() => {
    const saved = buildProjectData();
    const reopened = migrateProjectData(JSON.parse(JSON.stringify(saved))).data;
    return {
      version: reopened.version,
      format: reopened.format,
      types: reopened.lines.map(line => line.type),
      directionMeta: reopened.lines.find(line => line.lineId === 'rt-direction')?.importMeta,
      profile: reopened.importProfile,
    };
  });
  expect(roundTrip.version).toBe(6);
  expect(roundTrip.format).toBe('play');
  expect(roundTrip.types).toEqual(['act','scene','stage-direction','character','dialogue']);
  expect(roundTrip.directionMeta.detectedType).toBe('stage-direction');
  expect(roundTrip.profile.selectedFormat).toBe('play');

  let exportPayload = null;
  await page.route('**/api/export-pdf', async route => {
    exportPayload = JSON.parse(route.request().postData() || '{}');
    await route.fulfill({ status:200, contentType:'application/json', body:JSON.stringify({ok:true}) });
  });
  await page.evaluate(() => doExportPDF());
  expect(exportPayload.format).toBe('play');
  expect(exportPayload.roundTripVersion).toBe(1);
  expect(exportPayload.lines.map(line => line.type)).toEqual(['act','scene','stage-direction','character','dialogue']);
  expect(exportPayload.lines.find(line => line.type === 'stage-direction').text).toBe('Lights rise slowly.');
  expect(exportPayload.importProfile.selectedFormat).toBe('play');
});


test('uncertain imported elements are explicitly reviewed before opening', async ({ page, skript }) => {
  await page.evaluate(() => {
    const lines = _flagUncertainImportedElements([
      {type:'scene', text:'INT. CONTROL ROOM - NIGHT'},
      {type:'action', text:'MYSTERIOUS VOICE'},
      {type:'dialogue', text:'The signal is getting stronger.'},
    ], 'pdf');
    _showPDFReviewWizard(lines, {
      coverData:{title:'Uncertain Import'}, titleHint:'Uncertain Import',
      source:'pdf', sourceLabel:'PDF', reviewTitle:'Review PDF Import',
      formatDetection:{format:'film', confidence:92, uncertain:false},
    });
  });

  await page.locator('#pdf-review-next').click();
  await page.locator('#pdf-review-next').click();
  await page.locator('#pdf-review-next').click();
  await expect(page.locator('#pdf-review-progress')).toHaveText('Step 4 of 4');
  await expect(page.locator('[data-import-element-type]')).toHaveCount(1);
  await expect(page.locator('[data-import-element-type="2"]')).toHaveValue('dialogue');
  await page.locator('#pdf-review-next').click();

  await expect(page.locator('#pdf-review-wizard')).not.toHaveClass(/\bopen\b/);
  await expect(page.locator('.script-panel.active .script-line')).toHaveCount(3);
  await expect(page.locator('.script-panel.active .script-line').nth(1)).toHaveAttribute('data-type', 'character');
  await expect(page.locator('.script-panel.active .script-line.import-review')).toHaveCount(0);
  const saved = await page.evaluate(() => buildProjectData());
  expect(saved.importProfile.selectedFormat).toBe('film');
  expect(saved.lines[1].importMeta.detectedType).toBe('character');
  expect(saved.lines[1].importMeta.needsReview).toBe(false);
  expect(saved.lines[2].importMeta.reviewed).toBe(true);
});
