import { expect } from 'playwright/test';


export class SkriptPage {
  constructor(page) {
    this.page = page;
    this.activeLines = page.locator('.script-panel.active .script-line');
  }

  async open() {
    await this.page.addInitScript(() => {
      try {
        localStorage.clear();
        localStorage.setItem('sf-touch-notified', '1');
      } catch (_) {}
      window.__skriptPrintCalls = 0;
      window.print = () => {
        window.__skriptPrintCalls += 1;
        window.dispatchEvent(new Event('afterprint'));
      };
    });
    await this.page.goto('/');
    const skip = this.page.getByRole('button', { name: 'Skip — open blank script', exact: true });
    await expect(skip).toBeVisible();
    await skip.click();
    await expect(this.page.locator('#wizard-modal')).not.toHaveClass(/\bopen\b/);
    await expect(this.activeLines).toHaveCount(1);
  }

  async switchRibbon(panel) {
    const tab = this.page.locator(`.ribbon-tab[data-panel="${panel}"]`);
    await expect(tab).toBeVisible();
    await tab.click();
    await expect(tab).toHaveClass(/\bactive\b/);
  }

  async chooseElement(type) {
    const touch = await this.page.locator('html').evaluate(root => root.classList.contains('sf-touch'));
    await this.switchRibbon(touch ? 'edit' : 'home');
    const button = this.page.locator(`.ribbon-panel.active .el-btn[data-type="${type}"]`);
    await expect(button).toBeVisible();
    await button.click();
  }

  async loadLocalFile(filePath) {
    await this.switchRibbon('home');
    const chooserPromise = this.page.waitForEvent('filechooser');
    await this.page.getByTestId('open-script').click();
    const chooser = await chooserPromise;
    await chooser.setFiles(filePath);
  }

  async importFountain(filePath) {
    await this.switchRibbon('import');
    const chooserPromise = this.page.waitForEvent('filechooser');
    await this.page.getByTestId('import-fountain').click();
    const chooser = await chooserPromise;
    await chooser.setFiles(filePath);
  }
}
