const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');

const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');
const start = html.indexOf('function _groupPDFItems(');
const end = html.indexOf('function _filterHeaderFooter(', start);
assert.ok(start >= 0 && end > start, 'PDF classifier source is present');

const context = {};
vm.createContext(context);
vm.runInContext(html.slice(start, end), context);

const pageWidth = 612;
const rows = [
  { text: 'INT. STATION - NIGHT', x: 108, y: 100, page: 1 },
  { text: 'A near-empty platform.', x: 108, y: 116, page: 1 },
  // Production labels sometimes share the character column in shooting PDFs.
  { text: 'PAN IN', x: 288, y: 140, page: 1 },
  { text: '00:12:34:08', x: 288, y: 164, page: 1 },
  { text: 'IMAGE', x: 288, y: 188, page: 1 },
  { text: 'ARCHIVE FOOTAGE', x: 288, y: 212, page: 1 },
  { text: 'TIMESTAMP 00:14:22', x: 288, y: 236, page: 1 },
  // Deliberately left of the detected character column, with an extension.
  { text: 'DR. MAYA (V.O.)', x: 218, y: 268, page: 1 },
  { text: 'The last train has gone.', x: 180, y: 284, page: 1 },
  // Mixed-case cues need character placement, typography, and dialogue evidence.
  { text: 'Dr. Chen', x: 288, y: 316, page: 1, bold: true, fontKey: 'Courier-Bold' },
  { text: 'Check the timestamp again.', x: 180, y: 332, page: 1, fontKey: 'Courier' },
  // Unicode uppercase names must not be lost by an ASCII-only test.
  { text: 'ÉLODIE', x: 288, y: 364, page: 1, bold: true, fontKey: 'Courier-Bold' },
  { text: 'It belongs to us.', x: 180, y: 380, page: 1, fontKey: 'Courier' },
  // Deliberately far right: this used to be classified as a transition by x alone.
  { text: 'PORTER', x: 445, y: 412, page: 1 },
  { text: '(quietly)', x: 252, y: 428, page: 1 },
  { text: 'Not quite.', x: 180, y: 444, page: 1 },
  { text: 'CUT TO:', x: 445, y: 476, page: 1 },
];
const margins = context._detectMarginsIntel(rows, pageWidth);
assert.equal(margins.characterX, 288, 'dialogue-backed cues determine the character margin');

const result = context._classifyPDFLines(rows, margins, pageWidth);
assert.deepEqual(
  JSON.parse(JSON.stringify(result.map(item => [item.type, item.text]))),
  [
    ['scene', 'INT. STATION - NIGHT'],
    ['action', 'A near-empty platform.'],
    ['action', 'PAN IN'],
    ['action', '00:12:34:08'],
    ['action', 'IMAGE'],
    ['action', 'ARCHIVE FOOTAGE'],
    ['action', 'TIMESTAMP 00:14:22'],
    ['character', 'DR. MAYA (V.O.)'],
    ['dialogue', 'The last train has gone.'],
    ['character', 'DR. CHEN'],
    ['dialogue', 'Check the timestamp again.'],
    ['character', 'ÉLODIE'],
    ['dialogue', 'It belongs to us.'],
    ['character', 'PORTER'],
    ['parenthetical', '(quietly)'],
    ['dialogue', 'Not quite.'],
    ['transition', 'CUT TO:'],
  ]
);

const repaired = context._repairPDFElementTypes([
  { type: 'action', text: 'RILEY', _x: 300, _y: 100, _page: 1 },
  { type: 'action', text: 'We need to leave.', _x: 180, _y: 116, _page: 1 },
]);
assert.deepEqual(
  JSON.parse(JSON.stringify(repaired.map(item => item.type))),
  ['character', 'dialogue']
);

for (const label of ['PAN IN', '12:34:56', 'TIMESTAMP', 'TIMESTAMP 00:14:22', 'IMAGE', 'IMAGE 3', 'ARCHIVE', 'STOCK FOOTAGE']) {
  assert.equal(context._isPDFNonCharacterCue(label), true, `${label} is production metadata`);
  const protectedPair = context._repairPDFElementTypes([
    { type: 'action', text: label, _x: 300, _y: 100, _page: 1 },
    { type: 'action', text: 'The picture fills the screen.', _x: 180, _y: 116, _page: 1 },
  ]);
  assert.equal(protectedPair[0].type, 'action', `${label} must not be repaired into a character`);
}

console.log('PDF import character-cue regression tests passed.');
