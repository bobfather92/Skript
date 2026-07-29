const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');

class ClassList {
  constructor(names = []) { this.names = new Set(names); }
  contains(name) { return this.names.has(name); }
  add(name) { this.names.add(name); }
  remove(name) { this.names.delete(name); }
}

class Element {
  constructor(type = '', text = '', units = 1) {
    this.dataset = type ? { type } : {};
    this.textContent = text;
    this.classList = new ClassList(type ? ['script-line'] : []);
    this._className = type ? 'script-line' : '';
    this.units = units;
    this.parentNode = null;
    this.attributes = {};
  }
  get className() { return this._className; }
  set className(value) {
    this._className = value;
    this.classList = new ClassList(String(value).split(/\s+/).filter(Boolean));
  }
  get innerText() { return this.textContent; }
  set innerText(value) { this.textContent = value; }
  getBoundingClientRect() { return { height: this.units * 16 }; }
  setAttribute(name, value) { this.attributes[name] = value; }
  before(...nodes) {
    const index = this.parentNode.children.indexOf(this);
    nodes.forEach(node => { node.parentNode = this.parentNode; });
    this.parentNode.children.splice(index, 0, ...nodes);
  }
  after(...nodes) {
    const index = this.parentNode.children.indexOf(this) + 1;
    nodes.forEach(node => { node.parentNode = this.parentNode; });
    this.parentNode.children.splice(index, 0, ...nodes);
  }
}

class Container {
  constructor(children) {
    this.children = children;
    children.forEach(child => { child.parentNode = this; });
  }
  querySelectorAll(selector) {
    const classes = selector.split(',').map(part => part.trim().replace(/^\./, ''));
    return this.children.filter(child => classes.some(name => child.classList.contains(name)));
  }
}

function line(type, text, units = 1) { return new Element(type, text, units); }
function runPagination(children) {
  const container = new Container(children);
  const context = {
    getLinesContainer: () => container,
    activeTabId: 'test',
    ensureScriptLineId: line => (line.dataset.lineId ||= `line-${container.children.indexOf(line)}`),
    getComputedStyle: () => ({ marginTop: '0', marginBottom: '0' }),
    document: {
      createElement: () => new Element(),
      addEventListener: () => {},
    },
  };
  vm.createContext(context);

  const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');
  const constants = html.slice(
    html.indexOf('const CONTD_MORE ='),
    html.indexOf('function _legacyUpdateContdMore(')
  );
  const start = html.indexOf('function updateContdMore()', html.indexOf('function _legacyUpdateContdMore('));
  const end = html.indexOf('// Hook into the existing update pipeline', start);
  vm.runInContext(constants + html.slice(start, end), context);
  context.updateContdMore();
  const layoutStart = html.indexOf('function buildCanonicalPrintLayout(');
  const layoutEnd = html.indexOf('\nasync function doExportPDF()', layoutStart);
  vm.runInContext(html.slice(layoutStart, layoutEnd), context);
  container.printLayout = context.buildCanonicalPrintLayout(container);
  return container;
}

// A heading plus its first action would exceed line 58, so both start page 2.
const sceneDoc = runPagination([
  ...Array.from({ length: 56 }, () => line('notes', 'x')),
  line('scene', 'INT. OFFICE - DAY', 3),
  line('action', 'Maya enters.', 2),
]);
const scene = sceneDoc.children.find(item => item.dataset.type === 'scene');
const sceneIndex = sceneDoc.children.indexOf(scene);
assert.equal(sceneDoc.children[sceneIndex - 2].className, 'virtual-page-break');
assert.ok(scene.classList.contains('page-leading-line'));

// A short first action still must not leave a new slug line in the last few
// lines of the preceding page.
const orphanSceneDoc = runPagination([
  ...Array.from({ length: 54 }, () => line('notes', 'x')),
  line('scene', 'EXT. STREET - NIGHT', 2),
  line('action', 'Rain.', 1),
]);
const orphanScene = orphanSceneDoc.children.find(item => item.dataset.type === 'scene');
assert.equal(orphanSceneDoc.children[orphanSceneDoc.children.indexOf(orphanScene) - 2].className, 'virtual-page-break');

// A speech longer than a page splits only after two complete dialogue lines.
const speech = [
  ...Array.from({ length: 45 }, () => line('notes', 'x')),
  line('character', 'MAYA', 2),
  ...Array.from({ length: 30 }, (_, i) => line('dialogue', `Sentence ${i + 1}.`, 2)),
];
const dialogueDoc = runPagination(speech);
const more = dialogueDoc.children.find(item => item.className === 'more-mark');
const pageBreak = dialogueDoc.children[dialogueDoc.children.indexOf(more) + 1];
const contd = dialogueDoc.children[dialogueDoc.children.indexOf(pageBreak) + 2];
assert.equal(more.textContent, '(MORE)');
assert.equal(pageBreak.className, 'virtual-page-break');
assert.equal(contd.textContent, "MAYA (CONT'D)");

// A single wrapped dialogue paragraph remains one selectable/editable element.
// Page calculation must not truncate it or clone the overflow into a fragment.
const longSpeechText = Array.from({ length: 180 }, (_, i) => `word${i + 1}`).join(' ');
const wrappedDoc = runPagination([
  ...Array.from({ length: 10 }, () => line('notes', 'x')),
  line('character', 'MAYA', 2),
  line('dialogue', longSpeechText, 60),
]);
const wrappedDialogue = wrappedDoc.children.filter(item => item.dataset.type === 'dialogue');
assert.equal(wrappedDialogue.length, 1);
assert.equal(wrappedDialogue[0].textContent, longSpeechText);
assert.equal(wrappedDialogue[0].dataset.paginationFullText, undefined);
assert.ok(!wrappedDoc.children.some(item => item.className === 'pagination-dialogue-fragment'));
const exportedSpeech = wrappedDoc.printLayout
  .filter(item => item.type === 'dialogue')
  .map(item => item.text)
  .join(' ');
assert.equal(exportedSpeech, longSpeechText);

// New Act is a hard boundary: it begins page 2 even when page 1 has room.
const actDoc = runPagination([
  line('scene', 'INT. OPENING ROOM - DAY', 2),
  line('action', 'The opening act ends early.', 2),
  line('new-act', 'ACT TWO', 3),
  line('scene', 'EXT. SECOND ACT STREET - NIGHT', 2),
]);
const newAct = actDoc.children.find(item => item.dataset.type === 'new-act');
const newActIndex = actDoc.children.indexOf(newAct);
assert.equal(actDoc.children[newActIndex - 2].className, 'virtual-page-break');
assert.ok(newAct.classList.contains('page-leading-line'));
assert.ok(actDoc.printLayout.some((item, index, layout) =>
  item.type === 'new-act' && layout[index - 2]?.type === '_break'
));

console.log('BBC-style pagination regression tests passed.');
