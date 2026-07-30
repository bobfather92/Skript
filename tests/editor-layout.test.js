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
assert.ok(
  html.includes('body[data-format="tv"]   #acts-rg { display: flex; }'),
  'The Acts group must retain the same flex layout and label baseline as other ribbon groups',
);
const ribbonRule = html.split('#ribbon {', 2)[1].split('}', 1)[0];
assert.ok(
  ribbonRule.includes('user-select: none;') && ribbonRule.includes('-webkit-user-select: none;'),
  'Ribbon labels must not trigger the browser text-selection menu on double-click',
);
assert.ok(html.includes('font-style: normal; color: #1a1a1a;'), 'BBC parentheticals must use regular text');
assert.ok(html.includes('text-decoration: underline; letter-spacing: 0;'), 'BBC act headings must be underlined');
assert.ok(html.includes('.script-page[data-format="audio"] .script-line[data-type="character"]::after'), 'Radio cues must include a colon');
assert.ok(html.includes('font-family: Arial, Helvetica, sans-serif;'), 'BBC radio Scene Style must use Arial');
assert.ok(html.includes('break-before: page; page-break-before: always;'), 'BBC stage scenes must start on a new page');
console.log('BBC A4 editor layout regression tests passed.');
