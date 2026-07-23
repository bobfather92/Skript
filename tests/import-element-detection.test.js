const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');

const html = fs.readFileSync(path.join(__dirname, '..', 'ScriptForge.html'), 'utf8');
const start = html.indexOf('const IMPORT_ELEMENT_REVIEW_THRESHOLD');
const end = html.indexOf('function _flagUncertainImportedElements(', start);
assert.ok(start >= 0 && end > start, 'shared import element detector is present');

const context = {};
vm.createContext(context);
vm.runInContext(html.slice(start, end), context);

const refined = context._refineImportedElementTypes([
  { type: 'action', text: 'DR. ÉLODIE (V.O.)', _wordLeft: 2880, bold: true },
  { type: 'action', text: 'I found the missing page.', _wordLeft: 1440 },
  { type: 'action', text: 'MAYA & JON', _wordLeft: 2880 },
  { type: 'action', text: 'Together now.', _wordLeft: 1440 },
  { type: 'action', text: 'HARD CUT TO:', _wordLeft: 4320, _wordAlign: 'right' },
  { type: 'character', text: 'TIMESTAMP 00:14:22', _wordLeft: 2880 },
], 'word');

assert.deepEqual(
  JSON.parse(JSON.stringify(refined.map(line => [line.type, line.text]))),
  [
    ['character', 'DR. ÉLODIE (V.O.)'],
    ['dialogue', 'I found the missing page.'],
    ['character', 'MAYA & JON'],
    ['dialogue', 'Together now.'],
    ['transition', 'HARD CUT TO:'],
    ['action', 'TIMESTAMP 00:14:22'],
  ]
);
assert.equal(refined[0].importMeta.needsReview, false, 'layout-backed Unicode character cue is confident');
assert.equal(refined[4].importMeta.confidence, 99, 'recognised transition has strong evidence');

const flattened = context._refineImportedElementTypes([
  { type: 'character', text: 'RILEY' },
  { type: 'action', text: 'The first dialogue paragraph.' },
  { type: 'action', text: 'A possible continuation without layout evidence.' },
  { type: 'action', text: 'Riley crosses the room.', _wordBreakBefore: true },
], 'word');
assert.deepEqual(
  JSON.parse(JSON.stringify(flattened.map(line => line.type))),
  ['character', 'dialogue', 'dialogue', 'action']
);
assert.equal(flattened[2].importMeta.needsReview, true, 'ambiguous flattened continuation is flagged');

console.log('Contextual import element detection tests passed.');
