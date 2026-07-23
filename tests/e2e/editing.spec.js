import { test, expect } from './support/fixtures.js';


test('a user can write and change screenplay elements', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.nth(0).fill('INT. AUTOMATION LAB - DAY');
  await lines.nth(0).press('Enter');
  await expect(lines).toHaveCount(2);
  await expect(lines.nth(1)).toHaveAttribute('data-type', 'action');

  await lines.nth(1).fill('A status light turns green.');
  await lines.nth(1).press('Enter');
  await expect(lines).toHaveCount(3);

  await lines.nth(2).click();
  await skript.chooseElement('character');
  await expect(lines.nth(2)).toHaveAttribute('data-type', 'character');
  await lines.nth(2).fill('MAYA');
  await lines.nth(2).press('Enter');

  await expect(lines.nth(3)).toHaveAttribute('data-type', 'dialogue');
  await lines.nth(3).fill('The test is running.');
  await expect(lines).toHaveCount(4);
  await expect(lines).toHaveText([
    'INT. AUTOMATION LAB - DAY',
    'A status light turns green.',
    'MAYA',
    'The test is running.',
  ]);
});

test('the core editor remains usable at compact touch size', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'compact-touch', 'Compact-device check');
  await expect(page.locator('#ribbon')).toBeVisible();
  await expect(page.locator('.script-panel.active .script-page')).toBeVisible();
  const layout = await page.evaluate(() => ({
    viewportWidth: document.documentElement.clientWidth,
    bodyWidth: document.body.scrollWidth,
    pageWidth: document.querySelector('.script-panel.active .script-page')?.getBoundingClientRect().width || 0,
  }));
  expect(layout.bodyWidth).toBeLessThanOrEqual(layout.viewportWidth + 2);
  expect(layout.pageWidth).toBeGreaterThan(300);
});

test('Focus mode keeps the active script visible from side-by-side view', async ({ page, skript }) => {
  await skript.activeLines.first().fill('INT. FOCUS ROOM - DAY');
  await skript.switchRibbon('view');
  await page.evaluate(() => setPageView('sidebyside'));
  await page.locator('#btn-focus-mode').click();

  await expect(page.locator('body')).toHaveClass(/focus-mode/);
  await expect(page.locator('.script-panel.active .lines-container')).toBeVisible();
  await expect(page.locator('.script-panel.active .script-line').first()).toHaveText('INT. FOCUS ROOM - DAY');
  await expect(page.locator('.script-panel:not(.active)')).toBeHidden();

  await page.locator('#focus-exit-btn').click();
  await expect(page.locator('.sbs-page-box').first()).toContainText('INT. FOCUS ROOM - DAY');
});

test('Backspace at the start joins a paragraph to the previous element', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.first().click();
  await skript.chooseElement('action');
  await lines.first().fill('The door opens.');
  await lines.first().press('Enter');
  await lines.nth(1).fill('Maya enters.');
  await lines.nth(1).evaluate(line => {
    const range = document.createRange();
    range.selectNodeContents(line);
    range.collapse(true);
    const selection = window.getSelection();
    selection.removeAllRanges();
    selection.addRange(range);
  });
  await lines.nth(1).press('Backspace');

  await expect(lines).toHaveCount(1);
  await expect(lines.first()).toHaveText('The door opens. Maya enters.');
  await expect(lines.first()).toHaveAttribute('data-type', 'action');
});

test('Enter moves the rest of an Action into a new Action paragraph', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.first().click();
  await skript.chooseElement('action');
  await lines.first().fill('Maya opens the heavy door.');
  await lines.first().evaluate(line => {
    const offset = line.textContent.indexOf('heavy');
    const range = document.createRange();
    range.setStart(line.firstChild, offset);
    range.collapse(true);
    const selection = window.getSelection();
    selection.removeAllRanges();
    selection.addRange(range);
  });
  await page.keyboard.press('Enter');

  await expect(lines).toHaveCount(2);
  await expect(lines).toHaveText(['Maya opens the', 'heavy door.']);
  await expect(lines.nth(0)).toHaveAttribute('data-type', 'action');
  await expect(lines.nth(1)).toHaveAttribute('data-type', 'action');
  await expect(lines.nth(1)).toBeFocused();
});

test('explicit adjacent Action formatting offers separate or merged paragraphs', async ({ page, skript }) => {
  const lines = skript.activeLines;
  await lines.first().click();
  await skript.chooseElement('action');
  await lines.first().fill('Rain hammers the roof.');
  await lines.first().press('Enter');
  await lines.nth(1).fill('The lights fail.');
  await lines.nth(1).click();
  await skript.chooseElement('action');

  await expect(page.locator('#adjacent-element-confirm')).toBeVisible();
  await page.getByRole('button', { name: 'Merge with previous' }).click();
  await expect(lines).toHaveCount(1);
  await expect(lines.first()).toHaveText('Rain hammers the roof. The lights fail.');
});

test('Dialogue and following Action retain one screenplay line of spacing', async ({ page, skript }) => {
  await page.evaluate(() => {
    const container = getLinesContainer(activeTabId);
    container.replaceChildren();
    const dialogue = addLine(activeTabId, 'dialogue');
    dialogue.textContent = 'We should leave now.';
    const action = addLine(activeTabId, 'action');
    action.textContent = 'Maya reaches for the door.';
  });
  const gap = await page.evaluate(() => {
    const dialogue = document.querySelector('.script-panel.active .script-line[data-type="dialogue"]');
    const action = document.querySelector('.script-panel.active .script-line[data-type="action"]');
    return action.getBoundingClientRect().top - dialogue.getBoundingClientRect().bottom;
  });
  expect(gap).toBeGreaterThanOrEqual(15);
  expect(gap).toBeLessThanOrEqual(17);
});
