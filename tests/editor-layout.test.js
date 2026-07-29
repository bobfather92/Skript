const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');

for (const rule of [
  'padding: 96px 72px 96px 144px;',
  'line-height: 16px;      /* 12pt single-spaced Courier at 96dpi */',
  'margin-left: 192px;   /* BBC cue starts 3.5in from page left */',
  'padding-left: 96px;',
  'padding-right: 120px;',
  'padding-left: 144px;',
  'padding-right: 192px;',
  'LINES_PER_PAGE: 58',
]) {
  assert.ok(html.includes(rule), `Missing screenplay geometry rule: ${rule}`);
}

assert.ok(!html.includes('body[data-line-spacing="normal"]  .script-line { line-height: 1.75'));
const transitionRule = html.split('.script-line[data-type="transition"] {', 2)[1].split('}', 1)[0];
assert.ok(transitionRule.includes('text-align: right;'), 'Transitions must align to the right edge');
assert.ok(
  html.includes('body[data-format="film"] #acts-rg,'),
  'The New Act controls must be available in Film projects',
);
console.log('BBC A4 editor layout regression tests passed.');
