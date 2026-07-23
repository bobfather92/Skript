const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');

const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');
const start = html.indexOf('function _detectPDFScriptFormat(');
const end = html.indexOf('function _showPDFReviewWizard(', start);
assert.ok(start >= 0 && end > start, 'PDF format detector source is present');

const context = {};
vm.createContext(context);
vm.runInContext(html.slice(start, end), context);

const unknown = context._detectPDFScriptFormat([{type:'action', text:'A room. Someone waits.'}]);
assert.equal(unknown.uncertain, true);
assert.equal(unknown.confidence, 0);

const film = context._detectPDFScriptFormat([
  {text:'INT. OFFICE - DAY'}, {text:'EXT. ROAD - NIGHT'}, {text:'INT. CAR - CONTINUOUS'}
]);
assert.equal(film.format, 'film');
assert.equal(film.uncertain, false);

const numberedFilm = context._detectPDFScriptFormat([
  {text:'SCENE 12'}, {text:'INT. OFFICE - DAY'}, {text:'SCENE 13'}, {text:'EXT. ROAD - NIGHT'}
]);
assert.equal(numberedFilm.format, 'film', 'shooting-script scene numbers are not stage-play evidence');
assert.equal(numberedFilm.uncertain, false);

const tv = context._detectPDFScriptFormat([{text:'TEASER'}, {text:'ACT ONE'}, {text:'END OF ACT'}]);
assert.equal(tv.format, 'tv');
assert.equal(tv.uncertain, false);

const numberedTv = context._detectPDFScriptFormat([
  {text:'TEASER'}, {text:'SCENE 1'}, {text:'INT. LAB - NIGHT'}, {text:'ACT ONE'}, {text:'SCENE 2'}
]);
assert.equal(numberedTv.format, 'tv', 'TV scene numbers must not override TV act markers');

const play = context._detectPDFScriptFormat([{text:'ACT I'}, {text:'ENTER HAMLET'}, {text:'CURTAIN'}]);
assert.equal(play.format, 'play');
assert.equal(play.uncertain, false);

const modernPlay = context._detectPDFScriptFormat([
  {text:'DRAMATIS PERSONAE'}, {text:'ACT II - SCENE 3'}, {text:'LIGHTS UP'},
  {text:'HAMLET: Is this a dagger?'}, {text:'EXEUNT'}
]);
assert.equal(modernPlay.format, 'play');
assert.equal(modernPlay.uncertain, false);

const hourDrama = context._detectPDFScriptFormat([
  {text:'EPISODE TITLE'}, {text:'COLD OPEN'}, {text:'INT. TARDIS - NIGHT'},
  {text:'ACT ONE'}, {text:'END OF ACT ONE'}, {text:'TAG'}, {text:'END OF SHOW'}
]);
assert.equal(hourDrama.format, 'tv');
assert.equal(hourDrama.uncertain, false);

const reviewed = context._flagUncertainImportedElements([
  {type:'scene', text:'INT. LAB - NIGHT'},
  {type:'action', text:'MYSTERIOUS VOICE'},
  {type:'dialogue', text:'Do not turn around.'},
], 'pdf');
assert.equal(reviewed[0].importMeta.needsReview, false);
assert.equal(reviewed[1].importMeta.needsReview, true);
assert.equal(reviewed[2].importMeta.needsReview, true, 'orphan dialogue is flagged for review');

const formatted = context._applyPDFFormatConventions([
  {type:'action', text:'ACT ONE'}, {type:'action', text:'TAG'}
], 'tv');
assert.deepEqual(JSON.parse(JSON.stringify(formatted.map(line => line.type))), ['act-break', 'tag']);

console.log('PDF Film/TV/Play fallback detection tests passed.');
