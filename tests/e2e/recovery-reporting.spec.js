import { test, expect } from './support/fixtures.js';


test('Recovery Centre restores a separate unsaved copy', async ({ page, skript }) => {
  await skript.activeLines.first().fill('INT. RECOVERY TEST - NIGHT');
  await page.evaluate(async () => {
    await sfApiFetch('/api/start-session', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: '{}' });
    recovery.lastSentHash = null;
    await sendHeartbeat();
  });

  // Reproduce startup: Welcome is still open underneath the crash prompt.
  await page.evaluate(() => {
    openNewProjectWizard();
    document.getElementById('recovery-modal').classList.add('visible');
  });
  await page.getByRole('button', { name: 'Browse recovery copies' }).click();
  await expect(page.locator('#recovery-centre-modal')).toBeVisible();
  // The dialog deliberately confirms focus again on the next animation frame
  // because the crash prompt's trigger is removed during its click handler.
  await expect(page.getByRole('button', { name: 'Refresh' })).toBeFocused();
  const layerState = await page.evaluate(() => {
    const centre = document.getElementById('recovery-centre-modal');
    const welcome = document.getElementById('wizard-modal');
    const box = centre.querySelector('.modal').getBoundingClientRect();
    const topElement = document.elementFromPoint(box.left + box.width / 2, box.top + 20);
    return {
      centreZ: Number(getComputedStyle(centre).zIndex),
      welcomeZ: Number(getComputedStyle(welcome).zIndex),
      centreIsTop: centre.contains(topElement),
      focusInside: centre.contains(document.activeElement),
      welcomeInert: welcome.inert,
    };
  });
  expect(layerState.centreZ).toBeGreaterThan(layerState.welcomeZ);
  expect(layerState.centreIsTop).toBe(true);
  expect(layerState.focusInside).toBe(true);
  expect(layerState.welcomeInert).toBe(true);
  await expect(page.locator('.recovery-copy')).not.toHaveCount(0);
  await page.locator('#restore-recovery-btn').click();
  await expect(page.locator('#wizard-modal')).not.toHaveClass(/\bopen\b/);
  await expect(page.locator('.tab.active .tab-title')).toContainText('(Recovered)');
  await expect(page.locator('.tab.active')).toHaveClass(/has-unsaved/);
  expect(await page.evaluate(() => tabs.find(tab => tab.id === activeTabId)?.filePath)).toBe('');
  expect(await page.evaluate(() => document.querySelector('.cover-view.active .cover-title-input')?.value || tabs.find(tab => tab.id === activeTabId)?.title)).toContain('(Recovered)');
});


test('Report a Problem removes project titles, paths and email addresses', async ({ page, skript }) => {
  await page.evaluate(() => {
    showToast('Save failed for UNTITLED SCRIPT at C:\\Users\\Jake\\secret.script and jake@example.com');
    openProblemReport();
  });
  const preview = page.locator('#diagnostic-preview');
  await expect(page.locator('#problem-report-modal')).toBeVisible();
  await expect(preview).toContainText('[project title]');
  await expect(preview).not.toContainText('UNTITLED SCRIPT');
  await expect(preview).not.toContainText('C:\\Users\\Jake');
  await expect(preview).not.toContainText('jake@example.com');
});


test('closing a project with unsaved work requires confirmation', async ({ page, skript }) => {
  await skript.activeLines.first().fill('INT. UNSAVED ROOM - DAY');
  page.once('dialog', dialog => dialog.dismiss());
  await page.locator('.tab.active .tab-close').click();
  await expect(page.locator('.tab.active')).toHaveCount(1);
  await expect(page.locator('.tab.active')).toHaveClass(/has-unsaved/);
});
