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

const nativeCheckpoint = {
  checkpoint: {
    data: {
      'native-line-a': {
        type: 'Slugline',
        cache: { t: 'INT. NATIVE WRITERDUET PROJECT - DAY', l: 1700000000001 },
      },
      'native-line-b': {
        type: 'Action',
        cache: { t: 'A real checkpoint opens.', l: 1700000000002 },
      },
      'native-line-c': {
        type: 'EditDialogName',
        cache: { t: '\ue5e5\u0005MAYA\u0006\ue5e6', l: 1700000000003 },
      },
      'native-line-d': {
        type: 'EditDialogParen',
        cache: { t: '(relieved)', l: 1700000000004 },
      },
      'native-line-e': {
        type: 'EditDialogContent',
        cache: { t: 'That is the real\nformat and remains one', l: 1700000000005 },
      },
      'native-line-f': {
        type: 'EditDialogContent',
        cache: { t: 'editable paragraph.', l: 1700000000006 },
      },
    },
    dataStoreCheckpointIds: {
      checkpoint: {
        checkpointPath: 'duet/project/b/writerduet-branch/checkpoints/users/test/checkpoint.json',
      },
    },
  },
  setIds: { '.set_id': '-' },
};
const nativeResult = context._extractWriterDuetDocuments(nativeCheckpoint, 'Native WriterDuet Script');
assert.equal(nativeResult.documents.length, 1);
assert.equal(nativeResult.documents[0].writerDuetBranchId, 'writerduet-branch');
assert.equal(nativeResult.documents[0].writerDuetUpdatedAt, 1700000000006);
assert.deepEqual(
  JSON.parse(JSON.stringify(nativeResult.documents[0].lines.map(line => [line.type, line.text]))),
  [
    ['scene', 'INT. NATIVE WRITERDUET PROJECT - DAY'],
    ['action', 'A real checkpoint opens.'],
    ['character', 'MAYA'],
    ['parenthetical', '(relieved)'],
    ['dialogue', 'That is the real format and remains one editable paragraph.'],
  ],
);
assert.equal(nativeResult.documents[0].lines[4].importMeta.sourceIndexEnd, 5);

const reopenedWriterDuetLines = context._writerDuetNormaliseImportedLines([
  { type: 'character', text: '\ue5e5\u0005CARVALKO\u0006\ue5e6', lineId: 'saved-cue' },
  { type: 'dialogue', text: 'A saved speech was\nsplit in', lineId: 'saved-dialogue-a' },
  { type: 'dialogue', text: 'an earlier import.', lineId: 'saved-dialogue-b' },
]);
assert.deepEqual(
  JSON.parse(JSON.stringify(reopenedWriterDuetLines.map(line => [line.type, line.text]))),
  [
    ['character', 'CARVALKO'],
    ['dialogue', 'A saved speech was split in an earlier import.'],
  ],
);

assert.throws(
  () => context._extractWriterDuetDocuments({ documents: [{ title: 'Notes', lines: [{ type: 'unknown', text: 'Nothing' }] }] }),
  /No screenplay documents/,
);

console.log('WriterDuet project and line-type import tests passed.');
