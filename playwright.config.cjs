const fs = require('node:fs');
const path = require('node:path');
const { defineConfig } = require('playwright/test');

const python = process.env.PYTHON || (process.platform === 'win32' ? 'python' : 'python3');
const serverScript = path.join('tests', 'e2e', 'server.py');
const browserCandidates = [
  process.env.PW_EXECUTABLE_PATH,
  'C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe',
  'C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe',
  'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
  'C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe',
].filter(Boolean);
const browserExecutable = process.platform === 'win32'
  ? browserCandidates.find(candidate => fs.existsSync(candidate))
  : process.env.PW_EXECUTABLE_PATH;

module.exports = defineConfig({
  testDir: './tests/e2e',
  testMatch: '**/*.spec.js',
  globalTeardown: require.resolve('./tests/e2e/teardown.cjs'),
  outputDir: 'test-results/e2e-artifacts',
  fullyParallel: false,
  workers: 1,
  retries: process.env.CI ? 2 : 0,
  timeout: 45_000,
  expect: { timeout: 7_000 },
  reporter: [
    ['list'],
    ['html', { outputFolder: 'test-results/e2e-report', open: 'never' }],
    ['json', { outputFile: 'test-results/e2e-results.json' }],
    ['junit', { outputFile: 'test-results/e2e-results.xml' }],
  ],
  use: {
    baseURL: 'http://127.0.0.1:4173',
    browserName: 'chromium',
    launchOptions: browserExecutable ? { executablePath: browserExecutable } : undefined,
    headless: true,
    actionTimeout: 10_000,
    navigationTimeout: 30_000,
    screenshot: 'only-on-failure',
    trace: 'retain-on-failure',
    video: process.env.PW_VIDEO ? 'retain-on-failure' : 'off',
    acceptDownloads: true,
  },
  projects: [
    {
      name: 'desktop-chromium',
      use: { viewport: { width: 1440, height: 900 } },
    },
    {
      name: 'compact-touch',
      use: {
        viewport: { width: 800, height: 600 },
        hasTouch: true,
        deviceScaleFactor: 1,
      },
    },
  ],
  webServer: {
    command: `"${python}" "${serverScript}"`,
    url: 'http://127.0.0.1:4173/api/version',
    timeout: 30_000,
    reuseExistingServer: false,
    stdout: 'pipe',
    stderr: 'pipe',
  },
});
