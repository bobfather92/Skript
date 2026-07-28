const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');
const start = html.indexOf('const WRITERDUET_TYPE_MAP');
const end = html.indexOf('async function _readWriterDuetFile(', start);
assert.ok(start >= 0 && end > start, 'WriterDuet parser source is present');

const context = { window: {} };
vm.createContext(context);
vm.runInContext(html.slice(start, end), context);

const project = {
  project: {
    title: 'The Glass Room Series',
    documents: [
      {
        title: 'Title Page',
        lines: [
          { lineType: 'Title', text: 'THE GLASS ROOM' },
          { lineType: 'Written By', text: 'Jamie Writer' },
        ],
      },
      {
        title: 'Pilot',
        content: [
          { id: 'wd-1', lineType: 'Scene Heading', content: 'INT. GLASS ROOM - NIGHT' },
          { id: 'wd-2', lineType: 'Action', content: [{ insert: 'Rain crosses the windows.' }] },
          { id: 'wd-3', lineType: 'Character', text: 'MAYA' },
          { id: 'wd-4', lineType: 'Parenthetical', text: '(quietly)' },
          { id: 'wd-5', lineType: 'Dialogue', text: 'We are not alone.' },
          { id: 'wd-6', lineType: 'Transition', text: 'CUT TO:' },
        ],
      },
      {
        name: 'Episode Two',
        lines: [
          ['Scene', 'EXT. EMPTY ROAD - DAWN'],
          ['Action', 'A single car approaches.'],
          ['Character Cue', 'MAYA'],
          ['Dialog', 'Keep moving.'],
        ],
      },
    ],
  },
};

const result = context._extractWriterDuetDocuments(project, 'Fallback');
assert.equal(result.projectTitle, 'The Glass Room Series');
assert.equal(result.documents.length, 2);
assert.deepEqual(
  JSON.parse(JSON.stringify(result.documents.map(document => document.title))),
  ['Pilot', 'Episode Two'],
);
assert.equal(result.documents[0].cover.author, 'Jamie Writer');
assert.deepEqual(
  JSON.parse(JSON.stringify(result.documents[0].lines.map(line => [line.type, line.text]))),
  [
    ['scene', 'INT. GLASS ROOM - NIGHT'],
    ['action', 'Rain crosses the windows.'],
    ['character', 'MAYA'],
    ['parenthetical', '(quietly)'],
    ['dialogue', 'We are not alone.'],
    ['transition', 'CUT TO:'],
  ],
);
assert.equal(result.documents[0].lines[0].lineId, 'wd-1');
assert.equal(result.documents[0].lines[0].importMeta.source, 'writerduet');
assert.equal(result.documents[0].lines[0].importMeta.confidence, 100);
assert.deepEqual(
  JSON.parse(JSON.stringify(result.documents[1].lines.map(line => line.type))),
  ['scene', 'action', 'character', 'dialogue'],
);

assert.throws(
  () => context._extractWriterDuetDocuments({ documents: [{ title: 'Notes', lines: [{ type: 'unknown', text: 'Nothing' }] }] }),
  /No screenplay documents/,
);

console.log('WriterDuet project and line-type import tests passed.');
