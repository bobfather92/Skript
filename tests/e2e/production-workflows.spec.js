import { test, expect } from './support/fixtures.js';
import path from 'node:path';
import fs from 'node:fs/promises';


test('a new storyboard starts linked and can import only selected scenes', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.nth(0).fill('INT. FIRST ROOM - DAY');
  await lines.nth(0).press('Enter');
  await lines.nth(1).fill('WIDE SHOT of the first room.');
  await lines.nth(1).press('Enter');
  await lines.nth(2).click();
  await skript.chooseElement('scene');
  await lines.nth(2).fill('EXT. SECOND STREET - NIGHT');

  await page.locator('.add-doc-btn').click();
  await page.getByTestId('add-storyboard').click();
  await page.getByRole('button', { name: 'Continue →' }).click();
  await page.getByRole('button', { name: 'Continue →' }).click();
  await page.getByRole('button', { name: 'Continue →' }).click();
  await page.getByRole('button', { name: /Create Storyboard/ }).click();
  await page.getByRole('button', { name: 'Use current scene' }).click();
  expect(await page.evaluate(() => {
    const sceneId = getStoryboardSceneRefs()[0].lineId;
    return sb.boards[0].frames.every(frame => frame.sceneLineId === sceneId);
  })).toBeTruthy();
  await expect(page.locator('#sb-storyboard-scenes-nav .sb-storyboard-scene-item', { hasText:'Unlinked frames' })).toHaveCount(0);

  await page.locator('#storyboard-board-rg').getByRole('button', { name: 'Link Shots' }).click();
  const picks = page.locator('#sb-link-scene-list input[type="checkbox"]');
  await expect(picks).toHaveCount(2);
  await picks.nth(1).uncheck();
  await page.locator('#sb-link-modal').getByRole('button', { name: 'Done' }).click();
  await expect(page.locator('#sb-storyboard-scenes-nav .sb-storyboard-scene-item', { hasText:'Scene 1' }).locator('.sb-storyboard-scene-count')).toHaveText('6');
  await expect(page.locator('#sb-storyboard-scenes-nav .sb-storyboard-scene-item', { hasText:'Scene 2' }).locator('.sb-storyboard-scene-count')).toHaveText('0');

  await page.locator('#storyboard-board-rg').getByRole('button', { name: 'Link Shots' }).click();
  await page.getByRole('button', { name: 'Clear all' }).click();
  await page.locator('#sb-link-modal').getByRole('button', { name: 'Done' }).click();
  await expect(page.locator('#sb-link-modal')).toHaveClass(/open/);
  expect(await page.evaluate(() => new Set(sb.boards[0].frames.map(frame => frame.sceneLineId)).size)).toBe(1);
  await picks.nth(0).check();
  await page.locator('#sb-link-modal').getByRole('button', { name: 'Done' }).click();
});

test('Writing mode keeps production-only and archived tools out of the default surface', async ({ page, skript }) => {
  await expect(page.locator('body')).toHaveAttribute('data-workspace-mode', 'writing');
  await expect(page.locator('.ribbon-tab[data-panel="production"]')).toBeHidden();
  await expect(page.locator('.ribbon-tab[data-panel="studio"]')).toBeHidden();

  await page.locator('.add-doc-btn').click();
  await expect(page.locator('#add-doc-menu')).toContainText('Outline & Beats');
  await expect(page.locator('#add-doc-menu')).toContainText('Catalogue & Breakdown');
  await expect(page.locator('#add-doc-menu')).not.toContainText('Scene Report');
  await expect(page.locator('#add-doc-menu')).not.toContainText('Journey Map');
  await expect(page.locator('#add-doc-menu')).not.toContainText('BD Report');

  await page.locator('#workspace-mode-switch button[data-workspace="production"]').click();
  await expect(page.locator('.ribbon-tab[data-panel="production"]')).toBeVisible();
  await expect(page.locator('.ribbon-tab[data-panel="studio"]')).toBeVisible();
  await expect(page.locator('.format-tv-only').first()).toBeHidden();
  await expect(page.locator('#btn-cloud-sync')).toContainText('Backup Folder');
});

test('a user can build a call sheet from script scenes and cast', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.nth(0).fill('INT. CONTROL ROOM - NIGHT');
  await lines.nth(0).press('Enter');
  await lines.nth(1).fill('Banks of monitors glow.');
  await lines.nth(1).press('Enter');
  await lines.nth(2).click();
  await skript.chooseElement('character');
  await lines.nth(2).fill('MAYA');
  await lines.nth(2).press('Enter');
  await lines.nth(3).fill('Bring the unit in.');

  await page.locator('.add-doc-btn').click();
  await page.getByTestId('add-call-sheet').click();
  await expect(page.locator('#production-hub-area')).toHaveClass(/active/);
  await expect(page.locator('.ph-header')).toContainText('Stripboard & Shooting Schedule');
  await page.getByRole('button', { name: '+ Shoot Day' }).click();
  await page.locator('.ph-day-head input[type="date"]').fill('2026-07-15');
  await page.locator('.ph-day-head input[type="time"]').fill('18:00');
  await page.locator('.ph-day-head input[placeholder="Primary location"]').fill('Studio A');
  await page.locator('.ph-strip-pool .ph-strip').dragTo(page.locator('.ph-day-body'));
  await page.locator('.ph-day-head .top-btn', { hasText: 'Call Sheet' }).click();

  await expect(page.locator('#call-sheet-area')).toHaveClass(/active/);
  await expect(page.locator('.cs-page')).toContainText('CONTROL ROOM');
  await expect(page.locator('.cs-page')).toContainText('MAYA');
  await expect(page.locator('.cs-page')).toContainText('Studio A');
  await expect(page.locator('#sb-callsheet-count')).toHaveText('1 call sheet');
  const savedCallSheets = await page.evaluate(() => serializeCurrentProject().callSheets);
  expect(savedCallSheets.docs).toHaveLength(1);
  expect(savedCallSheets.docs[0].scenes[0].heading).toContain('CONTROL ROOM');
  expect(savedCallSheets.docs[0].crewCall).toBe('18:00');
});

test('PDF review confirms format, title, characters, and scenes before import', async ({ page, skript }) => {
  await page.evaluate(() => {
    const lines = [
      { type: 'action', text: 'TEASER' },
      { type: 'scene', text: 'INT. NEWSROOM - DAY' },
      { type: 'character', text: 'TIMESTAMP' },
      { type: 'dialogue', text: '10:42:03' },
      { type: 'character', text: 'MAYA' },
      { type: 'dialogue', text: 'We are live.' },
    ];
    const formatDetection = _detectPDFScriptFormat(lines);
    _showPDFReviewWizard(lines, { coverData: { title: 'Imported Draft' }, titleHint: 'Imported Draft', formatDetection });
  });
  await expect(page.locator('#pdf-review-wizard')).toHaveClass(/open/);
  await expect(page.locator('#pdf-r-format')).toHaveValue('tv');
  await page.locator('#pdf-r-title').fill('Reviewed Episode');
  await page.locator('#pdf-review-next').click();
  const timestampRow = page.locator('.pdf-review-row').filter({ has: page.locator('input[value="TIMESTAMP"]') });
  await expect(timestampRow).toHaveCount(0); // production labels are rejected as character cues automatically
  await expect(page.locator('.pdf-review-row').filter({ has: page.locator('input[value="MAYA"]') })).toHaveCount(1);
  await page.locator('#pdf-review-next').click();
  await page.locator('#pdf-review-next').click();
  await page.locator('#pdf-review-next').click();

  await expect(page.locator('.tab.active .tab-title')).toHaveText('Reviewed Episode');
  await expect(page.locator('.script-panel.active .script-page')).toHaveAttribute('data-format', 'tv');
  await expect(skript.activeLines.filter({ hasText: 'TIMESTAMP' })).toHaveAttribute('data-type', 'action');
  await expect(skript.activeLines.filter({ hasText: 'MAYA' })).toHaveAttribute('data-type', 'character');
  await expect.poll(() => page.evaluate(() => serializeCurrentProject().format)).toBe('tv');
});

test('DOCX import uses the built-in reader when the desktop service is unavailable', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'desktop-chromium', 'The built-in DOCX path is covered once on desktop');
  const docxFixture = 'UEsDBBQAAAAIAJVo7lzVa5JsYAEAAE4DAAARAAAAd29yZC9kb2N1bWVudC54bWyVU01TwjAQvfMrMjnpgRY9OE6HlmEQLX4AI2Ucj6Fd24xpUpOF2n9vWsXhkFG4JJvJy9vdty/D0WcpyA604UqG9MIbUAIyVRmXeUjXyW3/mhKDTGZMKAkhbcDQUdQb1kGm0m0JEollkCaoQ1ogVoHvm7SAkhlPVSDt3ZvSJUN71LlfK51VWqVgjE1QCv9yMLjyS8YljSzlRmVN1CPEhlV7rpa621bYCCB1sGMipAlHAdSPhv4voFswSuIpmTwuJg8kXqxX0xaAHUx/gw+pf568aI4IkmyaY9D3rORAEjAI+n/8RtuSsamsahXL9yU70M42VylIiIG1k3B2O5sn3mG7pE/ms7s4OaaRZ6u4Havm72AIFjYpl5mqjffnY2edk4JpllpBnEU+jV/Hp3MumbbGKgB5yoST9+xjywFFc346+Q23Vs63bgvNkBTMtI7XCBlhuRXKJUq7dW5tg/1PiL4AUEsDBBQAAAAIAJVo7lxxObEi6QAAAFwCAAAPAAAAd29yZC9zdHlsZXMueG1snZFBTsMwEEX3PYU1e+rCAqEoSRcgBDskygFGzpBYsseWxzTk9rioKaqyIjt73vf7sl3vv71TR0piAzdwu92BIjahs9w38HF4vnkAJRm5QxeYGphIYN9u6rGSPDkSVc6zVGMDQ86x0lrMQB5lGyJxYZ8hecxlm3o9htTFFAyJFL13+m63u9ceLUO7UWp2qrHKUyxdERP2CeMA6oxeuwYONjuCtqQZ/Sl8RDdPdVvrc/QfxndDTC+Ep0svxL9QzXRdweNQxiZTWtj/yDrzGybiPFC2Bt3Cfk3XNTzZ8vP91/LFL+DKe1lK+wNQSwMEFAAAAAgAlWjuXPFnm3a5AAAAAwEAABEAAABkb2NQcm9wcy9jb3JlLnhtbGXOvWrDQBAE4N5PcVxvreTCBHGSC4NxmcJ5gGVvIwnfH7drE799lBDUpBxm+Bh3+orBPLnKktNgu6a1hhNlv6RpsB+3y/7NGlFMHkNOPNgXiz2NO0elp1z5vebCVRcWs0JJeiqDnVVLDyA0c0Rp1kVay89cI+oa6wQF6Y4Tw6FtjxBZ0aMi/ID7sol292d62szyqOFX8AQcOHJSga7pwI7OU6+LBh5vM5tzyHQ31/wQdrA1Dv79Hr8BUEsBAhQAFAAAAAgAlWjuXNVrkmxgAQAATgMAABEAAAAAAAAAAAAAAIABAAAAAHdvcmQvZG9jdW1lbnQueG1sUEsBAhQAFAAAAAgAlWjuXHE5sSLpAAAAXAIAAA8AAAAAAAAAAAAAAIABjwEAAHdvcmQvc3R5bGVzLnhtbFBLAQIUABQAAAAIAJVo7lzxZ5t2uQAAAAMBAAARAAAAAAAAAAAAAACAAaUCAABkb2NQcm9wcy9jb3JlLnhtbFBLBQYAAAAAAwADALsAAACNAwAAAAA=';
  await page.evaluate(() => { window._SF_PORT = 0; });
  await page.locator('#word-import-input').setInputFiles({
    name: 'clock-house.docx',
    mimeType: 'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
    buffer: Buffer.from(docxFixture, 'base64'),
  });
  await expect(page.locator('#pdf-review-wizard')).toHaveClass(/open/);
  await expect(page.locator('#import-review-heading')).toHaveText('Review Word Import');
  await expect(page.locator('#pdf-r-title')).toHaveValue('THE CLOCK HOUSE');
  const filmChoice = page.locator('input[name="pdf-r-format-choice"][value="film"]');
  if (await filmChoice.count()) await filmChoice.check();
  await page.locator('#pdf-review-next').click();
  await page.locator('#pdf-review-next').click();
  await page.locator('#pdf-review-next').click();
  await page.locator('#pdf-review-next').click();
  await expect(page.locator('.tab.active .tab-title')).toHaveText('THE CLOCK HOUSE');
  await expect(skript.activeLines.filter({ hasText: 'INT. CLOCK HOUSE - NIGHT' })).toHaveAttribute('data-type', 'scene');
  await expect(skript.activeLines.filter({ hasText: 'MAYA' })).toHaveAttribute('data-type', 'character');

  const wrappedDialogue = 'This long speech remains one editable dialogue paragraph even when Word stores a soft line break inside it.';
  const softBreakDocx = await page.evaluate(async dialogueText => {
    if (!_ensureDocxEngine() || !docx?.JSZip) throw new Error('Word archive support is unavailable');
    const [firstHalf, secondHalf] = [
      'This long speech remains one editable dialogue paragraph',
      'even when Word stores a soft line break inside it.',
    ];
    const zip = new docx.JSZip();
    zip.file('word/document.xml', `<?xml version="1.0" encoding="UTF-8"?>
      <w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"><w:body>
        <w:p><w:pPr><w:pStyle w:val="SceneHeading"/></w:pPr><w:r><w:t>INT. IMPORT TEST - DAY</w:t></w:r></w:p>
        <w:p><w:pPr><w:pStyle w:val="Character"/></w:pPr><w:r><w:t>MAYA</w:t></w:r></w:p>
        <w:p><w:pPr><w:pStyle w:val="Dialogue"/></w:pPr><w:r><w:t>${firstHalf}</w:t><w:br/><w:t xml:space="preserve"> ${secondHalf}</w:t></w:r></w:p>
      </w:body></w:document>`);
    zip.file('word/styles.xml', `<?xml version="1.0" encoding="UTF-8"?>
      <w:styles xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">
        <w:style w:type="paragraph" w:styleId="SceneHeading"><w:name w:val="Scene Heading"/></w:style>
        <w:style w:type="paragraph" w:styleId="Character"><w:name w:val="Character"/></w:style>
        <w:style w:type="paragraph" w:styleId="Dialogue"><w:name w:val="Dialogue"/></w:style>
      </w:styles>`);
    zip.file('docProps/core.xml', `<?xml version="1.0" encoding="UTF-8"?>
      <cp:coreProperties xmlns:cp="http://schemas.openxmlformats.org/package/2006/metadata/core-properties"
        xmlns:dc="http://purl.org/dc/elements/1.1/"><dc:title>Wrapped Dialogue Test</dc:title></cp:coreProperties>`);
    const output = await zip.generateAsync({ type: 'base64', compression: 'DEFLATE' });
    if (dialogueText !== `${firstHalf} ${secondHalf}`) throw new Error('Dialogue fixture mismatch');
    return output;
  }, wrappedDialogue);
  await page.locator('#word-import-input').setInputFiles({
    name: 'wrapped-dialogue.docx',
    mimeType: 'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
    buffer: Buffer.from(softBreakDocx, 'base64'),
  });
  await expect(page.locator('#pdf-review-wizard')).toHaveClass(/open/);
  await expect.poll(() => page.evaluate(() =>
    pdfReviewState?.lines.filter(line => line.type === 'dialogue').map(line => line.text)
  )).toEqual([wrappedDialogue]);
  for (let step = 0; step < 4; step += 1) await page.locator('#pdf-review-next').click();
  await expect(page.locator('#pdf-review-wizard')).not.toHaveClass(/\bopen\b/);
  const importedDialogue = page.locator('.script-panel.active .script-line[data-type="dialogue"]');
  await expect(importedDialogue).toHaveCount(1);
  await expect(importedDialogue).toHaveText(wrappedDialogue);
});

test('Studio schedule links scenes, catalogue, reports and Call Sheets', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.nth(0).fill('INT. STUDIO FLOOR - DAY');
  await lines.nth(0).press('Enter');
  await lines.nth(1).fill('A camera PANS LEFT across the set.');
  await lines.nth(1).press('Enter');
  await lines.nth(2).click();
  await skript.chooseElement('character');
  await lines.nth(2).fill('MAYA');
  await lines.nth(2).press('Enter');
  await lines.nth(3).fill('Ready for the first setup.');

  await page.locator('#workspace-mode-switch button[data-workspace="production"]').click();
  await page.locator('.ribbon-tab[data-panel="studio"]').click();
  await page.locator('.ribbon-panel[data-panel="studio"] .rb', { hasText: 'Schedule' }).click();
  await expect(page.locator('#production-hub-area')).toHaveClass(/active/);
  await page.getByRole('button', { name: '+ Shoot Day' }).click();
  await page.locator('.ph-strip-pool .ph-strip').dragTo(page.locator('.ph-day-body'));
  await expect(page.locator('.ph-day-body .ph-strip')).toContainText('STUDIO FLOOR');
  await page.locator('.ph-day-head .top-btn', { hasText: 'Call Sheet' }).click();
  await expect(page.locator('#call-sheet-area')).toHaveClass(/active/);
  await expect(page.locator('.cs-page')).toContainText('STUDIO FLOOR');

  const production = await page.evaluate(() => serializeCurrentProject().production);
  expect(production.shootDays).toHaveLength(1);
  expect(production.shootDays[0].scenes).toHaveLength(1);
  expect(production.catalogue.some(item => item.type === 'cast' && item.name === 'MAYA')).toBeTruthy();
  expect(production.catalogue.some(item => item.type === 'location')).toBeTruthy();
});

test('FDX import preserves native paragraph types and validates round trip', async ({ page, skript }) => {
  await page.locator('#fdx-import-input').setInputFiles(path.join(process.cwd(), 'tests', 'e2e', 'fixtures', 'roundtrip-sample.fdx'));
  await expect(page.locator('.tab.active .tab-title')).toHaveText('FDX Interchange Test');
  await expect(skript.activeLines).toHaveCount(6);
  await expect(skript.activeLines.nth(0)).toHaveAttribute('data-type', 'scene');
  await expect(skript.activeLines.nth(2)).toHaveAttribute('data-type', 'character');
  await expect(skript.activeLines.nth(3)).toHaveAttribute('data-type', 'parenthetical');
  await expect(skript.activeLines.nth(5)).toHaveAttribute('data-type', 'transition');
  const result = await page.evaluate(() => validateFDXRoundTrip(buildFDXDocument()));
  expect(result.ok).toBeTruthy();
  expect(result.mismatches).toBe(0);
});

test('production documents follow stable scenes through edits, reordering, and deletion', async ({ page, skript }) => {
  const result = await page.evaluate(() => {
    clearTimeout(productionSyncTimer);
    const container = getLinesContainer(activeTabId);
    container.replaceChildren();
    const add = (type, text, lineId) => {
      const line = addLine(activeTabId, type);
      line.textContent = text;
      if (lineId) ensureScriptLineId(line, lineId);
      return line;
    };

    const sceneA = add('scene', 'INT. CONTROL ROOM - DAY', 'scene-control');
    add('action', 'Maya picks up the brass key.');
    add('character', 'MAYA');
    add('dialogue', 'Ready to begin.');
    const sceneB = add('scene', 'EXT. COURTYARD - NIGHT', 'scene-courtyard');
    add('action', 'A WIDE SHOT reveals the empty yard.');

    synchronizeProductionData({ reason: 'test-setup' });
    bdData['scene-control'].cats.props.push('Brass Key');
    productionState.outline['scene-control'] = { act:'1', storyline:'A', beat:'The test begins', arc:'Maya takes control' };
    productionState.continuity['scene-control'] = { coverage:[], takes:[], notes:'Key in right hand', camera:'', sound:'' };
    productionState.shootDays = [{
      id:'day-one', name:'Day 1', date:'2026-08-10', call:'07:00', location:'Studio A', moves:[], notes:'',
      scenes:[{ lineId:'scene-control', minutes:45 }, { lineId:'scene-courtyard', minutes:30 }]
    }];
    const sheet = newCallSheetData();
    Object.assign(sheet, { id:'sheet-one', sourceDayId:'day-one', title:'Sync Test', sceneIds:['scene-control','scene-courtyard'] });
    callSheetState.docs = [sheet];
    callSheetState.activeId = sheet.id;
    synchronizeProductionData({ reason: 'linked-documents' });

    const controlShot = SL.getShotRefs().find(shot => shot.sceneLineId === 'scene-control');
    sb.boards = [{
      id:1, name:'Board 1', orientation:'portrait', cols:3, captions:true, currentPage:0,
      frames:[{ ...makeStoryboardFrame(0), sceneLineId:'scene-control', shotId:controlShot?.id || null, caption:'Keep this artwork' }]
    }];
    sb.activeBoardId = 1;

    sceneA.textContent = 'INT. MAIN CONTROL - NIGHT';
    let line = sceneA.nextElementSibling;
    while (line && line.dataset.type !== 'scene') {
      if (line.dataset.type === 'character') line.textContent = 'JORDAN';
      line = line.nextElementSibling;
    }
    const sceneBBlock = [];
    line = sceneB;
    while (line) {
      sceneBBlock.push(line);
      line = line.nextElementSibling;
    }
    sceneBBlock.forEach(item => container.insertBefore(item, sceneA));
    updateSceneNumbers(activeTabId);
    synchronizeProductionData({ reason: 'rename-reorder' });

    const reorderedScenes = getProductionSceneRecords();
    const reorderedSheet = callSheetState.docs[0];
    const reordered = {
      order: reorderedScenes.map(scene => scene.lineId),
      breakdownNumber: bdData['scene-control'].number,
      breakdownProps: [...bdData['scene-control'].cats.props],
      callHeading: reorderedSheet.scenes.find(scene => scene.lineId === 'scene-control')?.heading,
      callCast: reorderedSheet.cast.map(row => row.role),
      shotSceneIndex: SL.getShotRefs().find(shot => shot.sceneLineId === 'scene-control')?.sceneIdx,
      storyboardSceneIndex: getStoryboardFrameContext(sb.boards[0].frames[0]).scene?.idx,
      outlineBeat: productionState.outline['scene-control']?.beat,
      continuityNote: productionState.continuity['scene-control']?.notes,
    };

    line = sceneA;
    while (line) {
      const next = line.nextElementSibling;
      line.remove();
      line = next;
    }
    updateSceneNumbers(activeTabId);
    synchronizeProductionData({ reason: 'delete-scene' });
    const frame = sb.boards[0].frames[0];
    const afterDelete = {
      scheduledIds: productionState.shootDays[0].scenes.map(item => item.lineId),
      callIds: callSheetState.docs[0].sceneIds,
      orphanOutline: productionState.orphanedScenes['scene-control']?.outline?.beat,
      orphanContinuity: productionState.orphanedScenes['scene-control']?.continuity?.notes,
      orphanBreakdown: productionState.orphanedScenes['scene-control']?.breakdown?.cats?.props || [],
      frameSceneId: frame.sceneLineId,
      frameCaption: frame.caption,
      orphanedFrameHeading: frame.orphanedScene?.heading,
    };
    return { reordered, afterDelete };
  });

  expect(result.reordered).toMatchObject({
    order: ['scene-courtyard', 'scene-control'],
    breakdownNumber: 2,
    callHeading: 'INT. MAIN CONTROL - NIGHT',
    shotSceneIndex: 2,
    storyboardSceneIndex: 2,
    outlineBeat: 'The test begins',
    continuityNote: 'Key in right hand',
  });
  expect(result.reordered.breakdownProps).toContain('Brass Key');
  expect(result.reordered.callCast).toContain('JORDAN');
  expect(result.afterDelete.scheduledIds).toEqual(['scene-courtyard']);
  expect(result.afterDelete.callIds).toEqual(['scene-courtyard']);
  expect(result.afterDelete.orphanOutline).toBe('The test begins');
  expect(result.afterDelete.orphanContinuity).toBe('Key in right hand');
  expect(result.afterDelete.orphanBreakdown).toContain('Brass Key');
  expect(result.afterDelete.frameSceneId).toBeNull();
  expect(result.afterDelete.frameCaption).toBe('Keep this artwork');
  expect(result.afterDelete.orphanedFrameHeading).toBe('INT. MAIN CONTROL - NIGHT');
});

test('real Final Draft files and advanced FDX features survive round trip', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'desktop-chromium', 'The complete FDX corpus is exercised once on desktop');
  const fixtureDir = path.join(process.cwd(), 'tests', 'e2e', 'fixtures');
  const corpus = [['real-final-draft-v5.fdx', '5'], ['real-fade-in.fdx', '2']];

  for (const [filename, expectedVersion] of corpus) {
    const xml = await fs.readFile(path.join(fixtureDir, filename), 'utf8');
    const result = await page.evaluate(source => {
      const parsed = parseFDXDocument(source);
      return {
        title:parsed.title, version:parsed.fdx.version, count:parsed.lines.length,
        sceneNumbers:parsed.lines.filter(line => line.type === 'scene').map(line => line.fdx.number),
        passthrough:parsed.fdx.passthrough.map(section => section.name),
      };
    }, xml);
    expect(result.title).toBe('FDX Test Script');
    expect(result.version).toBe(expectedVersion);
    expect(result.count).toBeGreaterThan(15);
    expect(result.sceneNumbers).toEqual(['1', '2']);
    expect(result.passthrough).toContain('ElementSettings');
  }

  await page.locator('#fdx-import-input').setInputFiles(path.join(fixtureDir, 'real-final-draft-v5.fdx'));
  await expect(page.locator('.tab.active .tab-title')).toHaveText('FDX Test Script');
  const realRoundTrip = await page.evaluate(() => {
    const xml = buildFDXDocument(true);
    const validation = validateFDXRoundTrip(xml);
    const reparsed = parseFDXDocument(xml);
    return {
      ok:validation.ok, mismatches:validation.mismatches, version:reparsed.fdx.version,
      sceneNumbers:reparsed.lines.filter(line => line.type === 'scene').map(line => line.fdx.number),
      hasElementSettings:reparsed.fdx.passthrough.some(section => section.name === 'ElementSettings'),
      preservedTitleLayout:xml.includes('<HeaderAndFooter') && xml.includes('Style="Underline">FDX Test Script'),
      hasHeader:xml.includes('<HeaderAndFooter'), hasUnderline:xml.includes('Style="Underline"'),
      coverSignature:_fdxCoverSignature(getCoverData(activeTabId)),
      originalSignature:_fdxCoverSignature(tabs.find(tab => tab.id === activeTabId)?.fdx?.originalCover),
    };
  });
  expect(realRoundTrip.coverSignature).toBe(realRoundTrip.originalSignature);
  expect(realRoundTrip).toMatchObject({
    ok:true, mismatches:0, version:'5', sceneNumbers:['1','2'],
    hasElementSettings:true, preservedTitleLayout:true,
    hasHeader:true, hasUnderline:true,
  });

  await page.locator('#fdx-import-input').setInputFiles(path.join(fixtureDir, 'fdx-advanced-conformance.fdx'));
  await expect(page.locator('.tab.active .tab-title')).toHaveText('FDX Advanced Conformance');
  await expect(page.locator('.script-panel.active .dual-dialogue-wrap')).toHaveCount(1);
  const advanced = await page.evaluate(() => {
    const xml = buildFDXDocument(true);
    const validation = validateFDXRoundTrip(xml);
    const parsed = parseFDXDocument(xml);
    const scene = parsed.lines.find(line => line.type === 'scene');
    const action = parsed.lines.find(line => line.type === 'action');
    const dual = parsed.lines.find(line => line.type === 'dual-dialogue');
    return {
      ok:validation.ok, mismatches:validation.mismatches,
      sceneNumber:scene?.fdx.number, startsNewPage:scene?.fdx.startsNewPage,
      summary:scene?.fdx.scene?.summary, note:scene?.fdx.notes?.[0]?.text,
      actionStyles:action?.fdx.runs.map(run => run.style),
      dualColumns:dual?.columns.map(column => column.map(line => `${line.type}:${line.text}`)),
      hasRevisions:parsed.fdx.passthrough.some(section => section.name === 'Revisions'),
      savedDual:buildProjectData().lines.some(line => line.type === 'dual-dialogue' && line.columns?.length === 2),
    };
  });
  expect(advanced).toMatchObject({
    ok:true, mismatches:0, sceneNumber:'12A', startsNewPage:'Yes',
    summary:'They make contact.', note:'Check the monitor continuity.', hasRevisions:true, savedDual:true,
    dualColumns:[
      ['character:MAYA','parenthetical:(into headset)','dialogue:We have them.'],
      ['character:JO','dialogue:Hold the channel.'],
    ],
  });
  expect(advanced.actionStyles).toEqual(['', 'Bold+Italic', '']);
});
