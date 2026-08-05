import { test, expect } from './support/fixtures.js';


test('script scenes, shots, and storyboard frames stay visibly connected', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.nth(0).fill('INT. EDIT SUITE - NIGHT');
  await lines.nth(0).press('Enter');
  await lines.nth(1).fill('CLOSE ON the monitor. PAN LEFT to reveal MAYA.');
  await expect(page.locator('#sb-shotlist-count')).toHaveText('2 shots');

  await page.locator('.add-doc-btn').click();
  await page.getByTestId('add-storyboard').click();
  await page.getByRole('button', { name: 'Continue →' }).click();
  await page.getByRole('button', { name: 'Continue →' }).click();
  await page.getByRole('button', { name: 'Continue →' }).click();
  await page.getByRole('button', { name: /Create Storyboard/ }).click();
  await expect(page.locator('#sb-link-modal')).toHaveClass(/open/);
  await page.locator('#sb-link-modal').getByRole('button', { name: 'Done' }).click();

  const frames = page.locator('.sb-frame');
  await expect(frames).toHaveCount(6);
  await expect(frames.nth(0).locator('.sb-frame-link-summary')).toContainText('Scene 1');
  await expect(frames.nth(0).locator('.sb-frame-link-summary')).toContainText('Shot 1');
  await expect(frames.nth(1).locator('.sb-frame-link-summary')).toContainText('Shot 2');
  await frames.nth(1).locator('.sb-canvas-wrap').click();
  if ((await page.viewportSize()).width <= 900) await page.evaluate(() => storyboardStudioTogglePane('inspector'));
  await expect(page.locator('.sb-studio-inspector').getByLabel('Scene link')).toHaveValue(/line-/);
  await expect(page.locator('.sb-studio-inspector').getByLabel('Shot List link')).toHaveValue(/sl\d+/);
  const storedFrame = await page.evaluate(() =>
    JSON.parse(localStorage.getItem('sf-storyboard')).boards[0].frames[1]
  );
  expect(storedFrame.sceneLineId).toMatch(/^line-/);
  expect(storedFrame.shotId).toMatch(/^sl\d+/);

  await page.locator('.add-doc-btn').click();
  await page.getByTestId('add-shot-list').click();
  const shotRows = page.locator('#sl-tbody tr.sl-row');
  await expect(shotRows.nth(0).locator('.sl-storyboard-link')).toHaveText('Frame 1');
  await expect(shotRows.nth(1).locator('.sl-storyboard-link')).toHaveText('Frame 2');

  await shotRows.nth(1).locator('.sl-storyboard-link').click();
  await expect(page.locator('#storyboard-area')).toHaveClass(/active/);
  await expect(page.locator('.sb-frame[data-frame-index="1"] .sb-frame-link-summary')).toContainText('Shot 2');
});
