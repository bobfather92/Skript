import { test, expect } from './support/fixtures.js';


test('bundled OCR recognises a locally rendered scanned PDF page', async ({ page, skript }, testInfo) => {
  test.skip(testInfo.project.name !== 'desktop-chromium', 'One full local OCR engine smoke test is sufficient.');
  test.setTimeout(60_000);

  const recognised = await page.evaluate(async () => {
    _pdfImportCancelled = false;
    const fakeScannedPdf = {
      numPages: 1,
      async getPage() {
        return {
          getViewport({ scale }) {
            return { width: 900 * scale, height: 300 * scale };
          },
          render({ canvasContext, viewport }) {
            canvasContext.save();
            canvasContext.fillStyle = '#000';
            canvasContext.font = `bold ${Math.round(viewport.height * 0.22)}px Arial`;
            canvasContext.fillText('INT. LAB - DAY', viewport.width * 0.08, viewport.height * 0.55);
            canvasContext.restore();
            return { promise: Promise.resolve() };
          },
          cleanup() {},
        };
      },
    };
    const items = await _ocrPDFPages(fakeScannedPdf, [1]);
    return items.map(item => item.text).join(' ');
  });

  expect(recognised.toUpperCase()).toContain('LAB');
  expect(recognised.toUpperCase()).toContain('DAY');
});
