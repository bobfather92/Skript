import { test, expect } from './support/fixtures.js';

test('Security opens above Share and Collaboration', async ({ page, skript }) => {
  await page.evaluate(() => {
    COLLAB.sessionId = 'visual-stack-test';
    document.getElementById('collab-modal').style.display = 'flex';
    openSecurityModal();
  });
  await expect(page.locator('#collab-modal')).toBeVisible();
  await expect(page.locator('#security-modal')).toBeVisible();
  const layers = await page.evaluate(() => ({
    collaboration: Number(getComputedStyle(document.getElementById('collab-modal')).zIndex),
    security: Number(getComputedStyle(document.getElementById('security-modal')).zIndex),
  }));
  expect(layers.security).toBeGreaterThan(layers.collaboration);
});

test('Script scenes can be collapsed and expanded in Navigator', async ({ page, skript }) => {
  const section = page.locator('#sb-scripts-section');
  const header = section.locator('.sidebar-section-header');
  await expect(section).toHaveClass(/open/);
  await header.click();
  await expect(section).not.toHaveClass(/open/);
  await header.click();
  await expect(section).toHaveClass(/open/);
});

test('Welcome screen uses one opaque colour plate', async ({ page, skript }) => {
  await page.evaluate(() => openNewProjectWizard());
  const result = await page.locator('#wizard-modal').evaluate(modal => {
    const selectors = ['#wiz-box', '#wiz-landing', '.wiz-landing-header', '.wiz-landing-btns', '.wiz-landing-skip-row'];
    const surfaces = selectors.map(selector => {
      const style = getComputedStyle(modal.querySelector(selector));
      return { background: style.backgroundColor, image: style.backgroundImage, opacity: style.opacity };
    });
    const rect = modal.getBoundingClientRect();
    return {
      surfaces,
      rect: { left: rect.left, top: rect.top, width: rect.width, height: rect.height },
      viewport: { width: innerWidth, height: innerHeight },
      modalBackground: getComputedStyle(modal).backgroundColor,
      bodyBackground: getComputedStyle(document.body).backgroundColor,
    };
  });
  const { surfaces } = result;
  expect(new Set(surfaces.map(item => item.background)).size).toBe(1);
  expect(surfaces.every(item => item.image === 'none' && item.opacity === '1')).toBe(true);
  expect(result.rect.left).toBe(0);
  expect(result.rect.top).toBe(0);
  expect(result.rect.width).toBe(result.viewport.width);
  expect(result.rect.height).toBe(result.viewport.height);
  expect(result.modalBackground).toBe(result.bodyBackground);
});

test('Welcome icon and Recent Projects align with the action cards', async ({ page, skript }) => {
  await page.evaluate(() => openNewProjectWizard());
  await page.waitForTimeout(200);
  await page.evaluate(() => {
    renderRecentScripts(Array.from({ length: 5 }, (_, index) => ({
      title: `Recent project ${index + 1}`,
      path: `C:\\Scripts\\Recent-${index + 1}.script`,
      savedAt: '2026-07-15T12:00:00Z',
    })));
  });
  await expect(page.locator('.wiz-brand-mark')).toHaveAttribute('src', '/favicon.png');
  await expect(page.getByText('Browse another location…', { exact: true })).toHaveCount(0);
  const widths = await page.locator('#wiz-landing').evaluate(landing => ({
    action: landing.querySelector('.wiz-primary-cta').getBoundingClientRect().width,
    recent: landing.querySelector('.wiz-recent-window').getBoundingClientRect().width,
    recentCount: landing.querySelectorAll('.wiz-recent-item').length,
    recentOverflow: getComputedStyle(landing.querySelector('#wiz-recent-list')).overflowY,
    openQuicklyHeight: landing.querySelector('.wiz-recent-head-actions > span').getBoundingClientRect().height,
    clearHeight: landing.querySelector('#wiz-clear-recent').getBoundingClientRect().height,
    openQuicklyFontSize: getComputedStyle(landing.querySelector('.wiz-recent-head-actions > span')).fontSize,
    clearFontSize: getComputedStyle(landing.querySelector('#wiz-clear-recent')).fontSize,
  }));
  expect(Math.abs(widths.action - widths.recent)).toBeLessThanOrEqual(1);
  expect(widths.recentCount).toBe(3);
  expect(widths.recentOverflow).toBe('visible');
  expect(widths.clearHeight).toBe(widths.openQuicklyHeight);
  expect(widths.clearFontSize).toBe(widths.openQuicklyFontSize);
});

test('Recent Projects can be cleared without deleting saved files', async ({ page, skript }) => {
  let clearRequests = 0;
  const recentProject = {
    title: 'Keep This Saved File',
    path: 'C:\\Scripts\\Keep-This-Saved-File.script',
    savedAt: '2026-07-15T12:00:00Z',
  };
  await page.route('**/api/recent-scripts', async route => {
    await route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ ok: true, scripts: [recentProject] }),
    });
  });
  await page.route('**/api/clear-recent', async route => {
    clearRequests += 1;
    await route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
  });
  await page.evaluate(() => openNewProjectWizard());
  const clearButton = page.locator('#wiz-clear-recent');
  await expect(clearButton).toBeVisible();
  await expect(clearButton).toBeEnabled();
  await clearButton.click();
  const confirmation = page.locator('#clear-recent-modal');
  await expect(confirmation).toBeVisible();
  await expect(confirmation).toContainText('Your saved project files will remain on this computer.');
  await confirmation.getByRole('button', { name: 'Clear recent projects' }).click();
  await expect.poll(() => clearRequests).toBe(1);
  await expect(confirmation).toBeHidden();
  await expect(page.locator('#wiz-recent-list')).toContainText('No recent projects yet.');
  await expect(clearButton).toBeDisabled();
});

test('a native close request opens the Skript close prompt instead of Edge', async ({ page, skript }) => {
  let windowAction = '';
  await page.route('**/api/window', async route => {
    windowAction = route.request().postDataJSON()?.action || '';
    await route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
  });
  await skript.activeLines.first().fill('INT. UNSAVED ROOM - NIGHT');
  await page.request.post('/__e2e_window_event');
  const modal = page.locator('#desktop-close-modal');
  await expect(modal).toBeVisible();
  await expect(modal).toContainText('Do you want to exit Skript?');
  await expect(modal).toContainText('1 project has unsaved changes. Save now to keep your latest work.');
  await expect(modal.getByRole('button', { name: 'Save and exit' })).toBeVisible();
  await expect(modal.getByRole('button', { name: 'Exit without saving' })).toBeVisible();
  const closeLayout = await modal.evaluate(element => {
    const box = element.querySelector('.modal-box').getBoundingClientRect();
    const copy = element.querySelector('.desktop-close-copy').getBoundingClientRect();
    const buttons = [...element.querySelectorAll('.desktop-close-actions button')].map(button => button.getBoundingClientRect());
    return {
      copyInside: copy.left >= box.left && copy.right <= box.right,
      buttonsInside: buttons.every(button => button.left >= box.left && button.right <= box.right),
      oneRow: new Set(buttons.map(button => Math.round(button.top))).size === 1,
    };
  });
  expect(closeLayout).toEqual({ copyInside: true, buttonsInside: true, oneRow: true });
  await modal.getByRole('button', { name: 'Continue writing' }).click();
  await expect(modal).toBeHidden();
  await expect(skript.activeLines.first()).toHaveText('INT. UNSAVED ROOM - NIGHT');
  await page.evaluate(() => requestDesktopClose());
  await modal.getByRole('button', { name: 'Exit without saving' }).click();
  await expect.poll(() => windowAction).toBe('close');
  await page.request.post('/__e2e_clear_window_event');
});

test('Save and exit saves the project before requesting native close', async ({ page, skript }) => {
  let windowAction = '';
  const closeSequence = [];
  await page.route('**/api/save-auto', async route => {
    closeSequence.push('save');
    await route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ ok: true, path: 'C:\\Users\\Tester\\Documents\\Skript\\Saved.script' }),
    });
  });
  await page.route('**/api/window', async route => {
    windowAction = route.request().postDataJSON()?.action || '';
    closeSequence.push(windowAction);
    await route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
  });
  await skript.activeLines.first().fill('INT. SAVE BEFORE CLOSE - DAY');
  await page.evaluate(() => requestDesktopClose());
  await page.locator('#desktop-close-modal').getByRole('button', { name: 'Save and exit' }).click();
  await expect.poll(() => windowAction).toBe('close');
  expect(closeSequence).toEqual(['save', 'close']);
});

test('View mode page glyphs fit inside the compact control plate', async ({ page, skript }, testInfo) => {
  const metrics = await page.locator('#page-view-bar').evaluate(bar => {
    const parent = bar.getBoundingClientRect();
    const read = id => {
      const rect = document.getElementById(id).getBoundingClientRect();
      return { left: rect.left, right: rect.right, top: rect.top, bottom: rect.bottom, width: rect.width, height: rect.height };
    };
    return {
      parent: { left: parent.left, right: parent.right, top: parent.top, bottom: parent.bottom },
      pageBreak: read('pv-btn-break'),
      sideBySide: read('pv-btn-sidebyside'),
      activeColour: getComputedStyle(document.getElementById('pv-btn-continuous')).color,
    };
  });
  const maximumControlHeight = testInfo.project.name === 'compact-touch' ? 44 : 20;
  for (const control of [metrics.pageBreak, metrics.sideBySide]) {
    expect(control.left).toBeGreaterThanOrEqual(metrics.parent.left);
    expect(control.right).toBeLessThanOrEqual(metrics.parent.right);
    expect(control.top).toBeGreaterThanOrEqual(metrics.parent.top);
    expect(control.bottom).toBeLessThanOrEqual(metrics.parent.bottom);
    expect(control.height).toBeLessThanOrEqual(maximumControlHeight);
  }
  expect(metrics.pageBreak.width).toBeLessThanOrEqual(22);
  expect(metrics.sideBySide.width).toBeLessThanOrEqual(26);
  const [red, green, blue] = metrics.activeColour.match(/[\d.]+/g).slice(0, 3).map(Number);
  expect(blue).toBeGreaterThan(red);
  expect(red).toBeGreaterThan(green);
});

test('PDF and Print All are neutral until hovered', async ({ page, skript }) => {
  await skript.switchRibbon('export');
  const pdf = page.getByTestId('export-pdf');
  const printAll = page.getByTestId('print-all');
  await expect(pdf).not.toHaveClass(/primary|active/);
  await expect(printAll).not.toHaveClass(/primary|active/);

  const resting = await pdf.evaluate(el => getComputedStyle(el).backgroundColor);
  await pdf.hover();
  const hovered = await pdf.evaluate(el => getComputedStyle(el).backgroundColor);
  expect(hovered).not.toBe(resting);
});

test('Add Document icons and labels share aligned columns', async ({ page, skript }) => {
  await page.locator('.add-doc-btn').click();
  const rows = page.locator('#add-doc-menu .add-doc-item');
  await expect(rows).toHaveCount(7);
  const positions = await rows.evaluateAll(items => items.map(item => {
    const icon = item.querySelector('.adi-icon').getBoundingClientRect();
    const label = item.querySelector('.adi-label').getBoundingClientRect();
    return { iconLeft: icon.left, iconWidth: icon.width, labelLeft: label.left };
  }));
  expect(new Set(positions.map(item => Math.round(item.iconLeft))).size).toBe(1);
  expect(new Set(positions.map(item => Math.round(item.iconWidth))).size).toBe(1);
  expect(new Set(positions.map(item => Math.round(item.labelLeft))).size).toBe(1);
});

test('editor and side-by-side pages use the PDF layout metrics without clipping page one', async ({ page, skript }) => {
  await skript.activeLines.first().fill('INT. LAYOUT TEST - DAY');
  const editorMetrics = await page.locator('.script-panel.active .script-page').evaluate(pageEl => {
    const line = pageEl.querySelector('.script-line');
    const pageStyle = getComputedStyle(pageEl);
    const lineStyle = getComputedStyle(line);
    return {
      width: parseFloat(pageStyle.width),
      paddingLeft: parseFloat(pageStyle.paddingLeft),
      paddingRight: parseFloat(pageStyle.paddingRight),
      fontFamily: lineStyle.fontFamily,
      fontSize: parseFloat(lineStyle.fontSize),
      lineHeight: parseFloat(lineStyle.lineHeight),
    };
  });
  expect(editorMetrics.width).toBeCloseTo(794, 0);
  expect(editorMetrics.paddingLeft).toBeCloseTo(144, 0);
  expect(editorMetrics.paddingRight).toBeCloseTo(72, 0);
  expect(editorMetrics.fontFamily).toContain('Courier New');
  expect(editorMetrics.fontSize).toBeCloseTo(16, 0);
  expect(editorMetrics.lineHeight).toBeCloseTo(16, 0);

  await page.evaluate(() => setPageView('sidebyside'));
  await expect(page.locator('.sbs-page-box').first()).toBeVisible();
  const positions = await page.evaluate(() => {
    const panel = document.querySelector('.script-panel.active').getBoundingClientRect();
    const firstPage = document.querySelector('.sbs-page-box').getBoundingClientRect();
    return { panelLeft: panel.left, pageLeft: firstPage.left, pageRight: firstPage.right };
  });
  expect(positions.pageLeft).toBeGreaterThanOrEqual(positions.panelLeft);
  expect(positions.pageRight).toBeGreaterThan(positions.pageLeft);
});

test('Navigator long scenes wrap and character hover highlights script cues', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.nth(0).fill('INT. EXTRAORDINARILY LONG UNDERGROUND RESEARCH FACILITY CONTROL ROOM WITH GLASS OBSERVATION WINDOWS - NIGHT');
  await lines.nth(0).press('Enter');
  await lines.nth(1).click();
  await skript.chooseElement('character');
  await lines.nth(1).fill('MAYA');
  await lines.nth(1).press('Enter');
  await lines.nth(2).fill('We are still here.');

  const sceneItem = page.locator('#scene-nav-list .sn-item').first();
  await expect(sceneItem.locator('.sn-time')).toHaveText('NIGHT');
  await expect(sceneItem.locator('.sn-time')).toBeVisible();
  const navStyles = await sceneItem.locator('.sn-name').evaluate(el => {
    const style = getComputedStyle(el);
    return { whiteSpace: style.whiteSpace, overflow: style.overflow, height: el.getBoundingClientRect().height };
  });
  expect(navStyles.whiteSpace).toBe('normal');
  expect(navStyles.overflow).toBe('visible');
  expect(navStyles.height).toBeGreaterThan(12);

  await page.evaluate(() => switchActiveView('cover'));
  await expect(page.locator('.cover-view.active')).toBeVisible();
  await expect(page.locator('#acts-rg')).toBeHidden();
  const authoredLines = page.locator('.script-panel[data-tab-id] .script-line');

  const pageErrors = [];
  page.on('pageerror', error => pageErrors.push(error.message));
  await page.locator('#char-tracker-list .char-item', { hasText: 'MAYA' }).hover();
  expect(pageErrors).toEqual([]);
  await expect(authoredLines.nth(1)).toHaveClass(/char-nav-highlight/);
  const dialogueFlyout = page.locator('#char-dialogue-flyout');
  await expect(dialogueFlyout).toBeVisible();
  await expect(dialogueFlyout.locator('.char-dialogue-title')).toHaveText('MAYA');
  await expect(dialogueFlyout.locator('.char-dialogue-count')).toHaveText('1 speech in this script');
  await expect(dialogueFlyout.locator('.char-dialogue-scene')).toContainText('UNDERGROUND RESEARCH FACILITY');
  await expect(dialogueFlyout.locator('.char-dialogue-text')).toHaveText('We are still here.');

  await dialogueFlyout.locator('.char-dialogue-entry').click();
  await expect(page.locator('.script-panel.active')).toBeVisible();
  await expect(page.locator('body')).not.toHaveClass(/title-page-workspace-active/);
  expect(await page.locator('#acts-rg').evaluate(element => element.style.display)).not.toBe('none');
  await expect(lines.nth(2)).toBeFocused();
  await expect(dialogueFlyout).toBeHidden();
  await page.locator('#sidebar-header').hover();
  await expect(authoredLines.nth(1)).not.toHaveClass(/char-nav-highlight/);
});

test('Navigator can be resized wider or narrower by dragging its edge', async ({ page, skript }) => {
  const sidebar = page.locator('#sidebar');
  const handle = page.locator('#sidebar-resize-handle');
  await expect(handle).toBeVisible();

  const initialWidth = await sidebar.evaluate(el => el.getBoundingClientRect().width);
  const handleBox = await handle.boundingBox();
  expect(handleBox).toBeTruthy();

  await page.mouse.move(handleBox.x + handleBox.width / 2, handleBox.y + 24);
  await page.mouse.down();
  await page.mouse.move(handleBox.x + handleBox.width / 2 + 120, handleBox.y + 24, { steps: 6 });
  await page.mouse.up();

  const widerWidth = await sidebar.evaluate(el => el.getBoundingClientRect().width);
  expect(widerWidth).toBeGreaterThan(initialWidth + 70);
  await expect(handle).toHaveAttribute('aria-valuenow', String(Math.round(widerWidth)));
  const tabbarPadding = await page.locator('#tabbar').evaluate(el => parseFloat(getComputedStyle(el).paddingLeft));
  expect(tabbarPadding).toBeGreaterThan(widerWidth);

  const widerHandleBox = await handle.boundingBox();
  await page.mouse.move(widerHandleBox.x + widerHandleBox.width / 2, widerHandleBox.y + 24);
  await page.mouse.down();
  await page.mouse.move(widerHandleBox.x + widerHandleBox.width / 2 - 90, widerHandleBox.y + 24, { steps: 6 });
  await page.mouse.up();

  const narrowerWidth = await sidebar.evaluate(el => el.getBoundingClientRect().width);
  expect(narrowerWidth).toBeLessThan(widerWidth - 50);
});

test('storyboard deletion uses the Skript confirmation dialog', async ({ page, skript }) => {
  await page.evaluate(() => {
    sb.boards = [{ id: 901, name: 'Delete Test Board', cols: 2, orientation: 'portrait', frames: [], currentPage: 0 }];
    sb.activeBoardId = 901;
    renderStoryboard();
    showStoryboardArea();
  });
  await page.locator('.storyboard-workspace-tab').click();
  await page.locator('#storyboard-board-rg').getByRole('button', { name: 'Delete Storyboard' }).click();
  await expect(page.locator('#sb-delete-confirm')).toBeVisible();
  await expect(page.locator('#sb-del-msg')).toContainText('Delete Test Board');
  await page.locator('#sb-delete-confirm').getByRole('button', { name: 'Cancel' }).click();
  expect(await page.evaluate(() => sb.boards.length)).toBe(1);

  await page.locator('#storyboard-board-rg').getByRole('button', { name: 'Delete Storyboard' }).click();
  await page.locator('#sb-delete-confirm').getByRole('button', { name: 'Delete' }).click();
  await expect(page.locator('#sb-delete-confirm')).toBeHidden();
  expect(await page.evaluate(() => sb.boards.length)).toBe(0);
});
