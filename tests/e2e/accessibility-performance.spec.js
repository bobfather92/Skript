import { test, expect } from './support/fixtures.js';


test('workspace exposes keyboard and screen-reader semantics', async ({ page, skript }) => {
  await expect(page.locator('#editor-area')).toHaveAttribute('role', 'main');
  await expect(page.locator('#sidebar')).toHaveAttribute('role', 'navigation');
  await expect(page.locator('#tabbar')).toHaveAttribute('role', 'tablist');
  await expect(page.locator('.tab.active')).toHaveAttribute('role', 'tab');
  await expect(page.locator('.tab.active')).toHaveAttribute('aria-selected', 'true');
  await expect(skript.activeLines.nth(0)).toHaveAttribute('role', 'textbox');
  await expect(skript.activeLines.nth(0)).toHaveAttribute('aria-label', /screenplay element/);
  await expect(page.locator('.sf-skip-link')).toHaveAttribute('href', '#editor-area');

  await skript.activeLines.nth(0).fill('INT. ACCESSIBLE STAGE - DAY');
  const scene = page.locator('.sn-item');
  await expect(scene).toHaveCount(1);
  await expect(scene).toHaveAttribute('role', 'button');
  await expect(scene).toHaveAttribute('tabindex', '0');
  await scene.press('Enter');
  await expect(skript.activeLines.nth(0)).toBeFocused();

  await page.evaluate(() => showToast('Accessible status update'));
  await expect(page.locator('#sf-toast')).toHaveAttribute('role', 'status');
  await expect(page.locator('#sf-announcer')).toHaveText('Accessible status update');
});


test('rapid typing coalesces expensive document-wide updates', async ({ page, skript }) => {
  await skript.activeLines.nth(0).fill('INT. PERFORMANCE LAB - DAY');
  const counts = await page.evaluate(async () => {
    const result = { words: 0, sceneRows: 0, fullSceneRebuilds: 0, characters: 0 };
    const originalWords = window.updateWordPageCount;
    const originalScenes = window.updateSceneNav;
    const originalSceneLine = window.updateSceneNavLine;
    const originalCharacters = window.updateCharTracker;
    window.updateWordPageCount = (...args) => { result.words++; return originalWords(...args); };
    window.updateSceneNav = (...args) => { result.fullSceneRebuilds++; return originalScenes(...args); };
    window.updateSceneNavLine = (...args) => { result.sceneRows++; return originalSceneLine(...args); };
    window.updateCharTracker = (...args) => { result.characters++; return originalCharacters(...args); };
    const line = document.querySelector('.script-panel.active .script-line');
    for (let index = 0; index < 12; index++) line.dispatchEvent(new InputEvent('input', { bubbles: true }));
    await new Promise(resolve => setTimeout(resolve, 450));
    window.updateWordPageCount = originalWords;
    window.updateSceneNav = originalScenes;
    window.updateSceneNavLine = originalSceneLine;
    window.updateCharTracker = originalCharacters;
    return result;
  });
  expect(counts.words).toBe(1);
  expect(counts.sceneRows).toBe(1);
  expect(counts.fullSceneRebuilds).toBe(0);
  expect(counts.characters).toBe(0);
});


test('touch mode provides reliable target sizes', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'compact-touch', 'Touch-device check');
  await expect(page.locator('html')).toHaveClass(/sf-touch/);
  await page.locator('.ribbon-tab[data-panel="edit"]').click();
  const layout = await page.locator('.ribbon-panel.active .el-btn').first().evaluate(element => {
    const rect = element.getBoundingClientRect();
    const next = element.parentElement?.nextElementSibling?.querySelector('.el-btn')?.getBoundingClientRect();
    const ribbon = document.querySelector('#ribbon-content')?.getBoundingClientRect();
    return {
      width: rect.width,
      height: rect.height,
      nextTop: next?.top,
      ribbonHeight: ribbon?.height,
    };
  });
  expect(layout.height).toBeGreaterThanOrEqual(44);
  expect(layout.nextTop).toBeCloseTo(await page.locator('.ribbon-panel.active .el-btn').first().evaluate(element => element.getBoundingClientRect().top), 0);
  expect(layout.ribbonHeight).toBeLessThanOrEqual(116);
});


test('touch ribbon separates file and editing commands without overflow', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'compact-touch', 'Touch-device check');
  const ribbon = page.locator('#ribbon-content');
  const overflow = async () => ribbon.evaluate(element => ({
    clientWidth: element.clientWidth,
    scrollWidth: element.scrollWidth,
  }));

  await expect(page.locator('.ribbon-tab[data-panel="edit"]')).toBeVisible();
  await expect(page.locator('.ribbon-panel[data-panel="home"] #elements-rg')).toBeHidden();
  expect(await page.locator('.ribbon-panel[data-panel="home"] .touch-home-hide').evaluateAll(elements =>
    elements.every(element => getComputedStyle(element).display === 'none')
  )).toBeTruthy();
  const homeLabels = await page.locator('.ribbon-panel[data-panel="home"] .rb-label').evaluateAll(labels =>
    labels.filter(label => label.closest('.rb').getClientRects().length > 0).map(label => label.textContent.trim())
  );
  expect(homeLabels).toEqual([
    'New', 'Open', 'Recent', 'Save', 'Save As', 'Options',
  ]);
  expect((await overflow()).scrollWidth).toBeLessThanOrEqual((await overflow()).clientWidth);

  await page.locator('.ribbon-tab[data-panel="edit"]').click();
  await expect(page.locator('.ribbon-panel[data-panel="edit"]')).toBeVisible();
  await expect(page.locator('#touch-elements-rg .el-btn')).toHaveCount(9);
  await expect(page.locator('.ribbon-panel[data-panel="edit"] .rb-label')).toHaveText(['Find', 'Options']);
  const editOverflow = await overflow();
  expect(editOverflow.scrollWidth).toBeLessThanOrEqual(editOverflow.clientWidth);
  const editLayout = await page.locator('.ribbon-panel[data-panel="edit"]').evaluate(panel => {
    const elements = Array.from(panel.querySelectorAll('#touch-elements-rg .el-btn'));
    const rects = elements.map(element => element.getBoundingClientRect());
    const tools = panel.querySelector('.touch-edit-tools').getBoundingClientRect();
    const panelRect = panel.getBoundingClientRect();
    return {
      minElementWidth: Math.min(...rects.map(rect => rect.width)),
      rows: new Set(rects.map(rect => Math.round(rect.top))).size,
      toolsRightGap: Math.round(panelRect.right - tools.right),
    };
  });
  expect(editLayout.minElementWidth).toBeGreaterThanOrEqual(88);
  expect(editLayout.rows).toBe(2);
  expect(editLayout.toolsRightGap).toBeLessThanOrEqual(1);

  const tabAlignment = await page.locator('.tab.active').evaluate(tab => {
    const tabRect = tab.getBoundingClientRect();
    const titleRect = tab.querySelector('.tab-title').getBoundingClientRect();
    return Math.abs((tabRect.top + tabRect.height / 2) - (titleRect.top + titleRect.height / 2));
  });
  expect(tabAlignment).toBeLessThanOrEqual(1);

  await page.evaluate(() => sfSetInputMode('mouse'));
  await expect(page.locator('.ribbon-tab[data-panel="home"]')).toHaveClass(/active/);
  await expect(page.locator('.ribbon-tab[data-panel="edit"]')).toBeHidden();
});


test('mouse mode keeps the standard ribbon dimensions', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'desktop-chromium', 'Desktop pointer check');
  await expect(page.locator('html')).toHaveClass(/(^|\s)sf-mouse(\s|$)/);
  await expect(page.locator('.ribbon-tab[data-panel="edit"]')).toBeHidden();
  await expect(page.locator('#ribbon-content')).toHaveCSS('height', '84px');
  const tabLayout = await page.locator('.tab.active').evaluate(tab => {
    const tabRect = tab.getBoundingClientRect();
    const titleRect = tab.querySelector('.tab-title').getBoundingClientRect();
    return {
      height: tabRect.height,
      titleOffset: Math.abs((tabRect.top + tabRect.height / 2) - (titleRect.top + titleRect.height / 2)),
    };
  });
  expect(tabLayout.height).toBeGreaterThanOrEqual(30);
  expect(tabLayout.titleOffset).toBeLessThanOrEqual(1);
});

test('Acts matches the other ribbon groups and cannot open the text-selection menu', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'desktop-chromium', 'Desktop ribbon check');
  const labels = page.locator('.ribbon-panel[data-panel="home"] .rg-label');
  const fileLabel = labels.filter({ hasText: /^File$/ });
  const elementsLabel = labels.filter({ hasText: /^Elements$/ });
  const actsLabel = labels.filter({ hasText: /^Acts$/ });
  await expect(actsLabel).toBeVisible();

  const layout = await page.locator('.ribbon-panel[data-panel="home"]').evaluate(panel => {
    const rect = text => {
      const label = Array.from(panel.querySelectorAll('.rg-label')).find(node => node.textContent.trim() === text);
      const bounds = label.getBoundingClientRect();
      return { top: bounds.top, bottom: bounds.bottom };
    };
    return {
      actsDisplay: getComputedStyle(panel.querySelector('#acts-rg')).display,
      file: rect('File'),
      elements: rect('Elements'),
      acts: rect('Acts'),
    };
  });
  expect(layout.actsDisplay).toBe('flex');
  expect(layout.acts.top).toBeCloseTo(layout.file.top, 0);
  expect(layout.acts.top).toBeCloseTo(layout.elements.top, 0);
  expect(layout.acts.bottom).toBeCloseTo(layout.file.bottom, 0);

  await actsLabel.dblclick();
  expect(await page.evaluate(() => window.getSelection()?.toString() || '')).toBe('');
  await expect(fileLabel).toHaveCSS('user-select', 'none');
  await expect(elementsLabel).toHaveCSS('user-select', 'none');
  await expect(actsLabel).toHaveCSS('user-select', 'none');
});


test('options exposes bundled open source licences', async ({ page, skript }) => {
  await page.evaluate(() => openOptions());
  await page.locator('#open-licenses-btn').click();
  await expect(page.locator('#licenses-modal')).toBeVisible();
  await expect(page.locator('#licenses-modal .opt-section')).toHaveCount(8);
  await expect(page.locator('#licenses-modal a[target="_blank"]')).toHaveCount(8);
  await expect(page.locator('#licenses-modal')).toContainText('PDF.js');
  await expect(page.locator('#licenses-modal')).toContainText('Tesseract.js 7.0.0');
  await expect(page.locator('#licenses-modal')).toContainText('Tesseract English trained data');
  await expect(page.locator('#licenses-modal')).toContainText('PyInstaller bootloader');
});


test('options shows the current release changes above licences', async ({ page, skript }) => {
  await page.evaluate(() => openOptions());
  const rows = page.locator('.opt-section:has(.cover-label:text-is("About")) .opt-row');
  await expect(rows.nth(0)).toContainText('Changes');
  await expect(rows.nth(1)).toContainText('Open source licences');
  await page.locator('#open-changes-btn').click();
  await expect(page.locator('#changes-modal')).toBeVisible();
  await expect(page.locator('#changes-modal')).toContainText('Multiple script imports');
  await expect(page.locator('#changes-modal')).toContainText('1.1.0.0');
  await expect(page.locator('#changes-modal [data-changes-version]')).toHaveCount(1);
  await expect(page.locator('#changes-modal [data-changes-panel]')).toHaveCount(1);
});


test('a persisted low-power profile removes costly effects', async ({ page }) => {
  await page.addInitScript(() => localStorage.setItem('sf-performance-mode', 'low'));
  await page.goto('/');
  await expect(page.locator('html')).toHaveClass(/sf-low-power/);
  await expect(page.locator('html')).toHaveAttribute('data-performance-tier', 'low');
  const blur = await page.locator('#wizard-modal').evaluate(element => getComputedStyle(element).backdropFilter);
  expect(blur === 'none' || blur === '').toBeTruthy();
});
