const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');
const marker = 'Accessibility/navigation controls remain available on screen';
const start = html.indexOf(marker);
assert.ok(start >= 0, 'PDF-only UI exclusion block exists');
const block = html.slice(start, start + 360);

for (const selector of ['.sf-skip-link', '#sf-announcer', '#page-view-bar', '#script-zoom-bar', '#sb-zoom-bar']) {
  assert.ok(block.includes(selector), `${selector} is excluded from PDF/print output`);
}
assert.ok(block.includes('display: none !important'), 'export-only controls are force-hidden');

// The controls themselves must remain in the live application for keyboard
// accessibility and page-view switching.
assert.ok(html.includes('<a class="sf-skip-link" href="#editor-area">Skip to script editor</a>'));
assert.ok(html.includes('<div id="page-view-bar">'));

// Browser-print cover pages must discard the on-screen 100%-height wrapper;
// otherwise the last contact rows fragment onto a second PDF page.
assert.ok(html.includes('body[data-print-mode] .cover-view[data-print-target="true"]'));
assert.ok(html.includes('height: auto !important; min-height: 0 !important; max-height: none !important'));
assert.ok(html.includes('function _prepareCoverPrintValues(coverEl)'));
assert.ok(html.includes("output.classList.add('cover-print-contact')"));

console.log('PDF export excludes accessibility and page-view UI chrome.');
