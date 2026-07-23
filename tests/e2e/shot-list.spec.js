import { test, expect } from './support/fixtures.js';


test('shot list follows scenes and camera directions as the writer edits', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.nth(0).fill('INT. STUDIO - DAY');
  await lines.nth(0).press('Enter');
  await lines.nth(1).fill('WIDE SHOT. PAN LEFT across the empty room.');

  await expect(page.locator('#sb-shotlist-count')).toHaveText('2 shots');

  await page.locator('.add-doc-btn').click();
  await page.getByTestId('add-shot-list').click();
  await expect(page.locator('#sl-panel')).toBeVisible();
  await expect(page.locator('#sl-count')).toHaveText('2 shots');
  await expect(page.locator('#sl-tbody tr.sl-row')).toHaveCount(2);
  await expect(page.locator('#sl-tbody')).toContainText('WS');
  await expect(page.locator('#sl-tbody')).toContainText('Pan Left');

  await page.locator('#sl-toolbar [title="Return to script editor"]').click();
  await lines.nth(1).fill('CLOSE ON the monitor. PUSH IN slowly.');
  await expect(page.locator('#sb-shotlist-count')).toHaveText('2 shots');

  await page.locator('.add-doc-btn').click();
  await page.getByTestId('add-shot-list').click();
  await expect(page.locator('#sl-tbody tr.sl-row')).toHaveCount(2);
  await expect(page.locator('#sl-tbody')).toContainText('CU');
  await expect(page.locator('#sl-tbody')).toContainText('Push In');
  await expect(page.locator('#sl-tbody')).not.toContainText('Pan Left');

  await page.locator('#sl-toolbar [title="Return to script editor"]').click();
  await lines.nth(1).click();
  await page.keyboard.press('End');
  await page.keyboard.press('Enter');
  await lines.nth(2).fill('CUTAWAY to a blinking archive light.');
  await expect(page.locator('#sb-shotlist-count')).toHaveText('3 shots');

  // Repeated input events update the same generated shot instead of duplicating it.
  await lines.nth(2).fill('CUTAWAY to a blinking archive light.');
  await expect(page.locator('#sb-shotlist-count')).toHaveText('3 shots');

  // Removing the camera direction also removes its generated shot.
  await lines.nth(2).fill('');
  await expect(page.locator('#sb-shotlist-count')).toHaveText('2 shots');
});
