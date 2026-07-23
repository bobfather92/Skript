import { test as base, expect } from 'playwright/test';
import { SkriptPage } from './skript-page.js';


export const test = base.extend({
  browserErrors: [async ({ page, baseURL }, use, testInfo) => {
    const errors = [];
    page.on('pageerror', error => errors.push(`pageerror: ${error.message}`));
    page.on('console', message => {
      if (message.type() === 'error') errors.push(`console: ${message.text()}`);
    });
    page.on('requestfailed', request => {
      if (request.url().startsWith(baseURL)) {
        errors.push(`requestfailed: ${request.method()} ${request.url()} - ${request.failure()?.errorText || 'unknown'}`);
      }
    });

    await use(errors);

    if (errors.length) {
      await testInfo.attach('browser-errors', {
        body: Buffer.from(errors.join('\n'), 'utf8'),
        contentType: 'text/plain',
      });
    }
    expect(errors, 'The workflow must not produce browser errors').toEqual([]);
  }, { auto: true }],

  skript: async ({ page }, use) => {
    const app = new SkriptPage(page);
    await app.open();
    await use(app);
  },
});

export { expect } from 'playwright/test';
