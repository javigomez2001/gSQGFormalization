// Smoke-test generated dashboard code offline, including provenance rendering.
// Usage: node blueprint/tools/tests/check_dashboard.js [blueprint.json]
const fs = require('fs');
const vm = require('vm');
const path = require('path');
const assert = require('assert');
const project = path.resolve(__dirname, '../../..');
const html = fs.readFileSync(path.join(project, 'blueprint/site/index.html'), 'utf8');
const script = html.match(/<script>([\s\S]*?)<\/script>/)[1];
const supplied = process.argv[2] || path.join(project, 'blueprint/site/data/blueprint.json');
const data = JSON.parse(fs.readFileSync(supplied, 'utf8'));
for (const mode of ["current", "source", "historical"]) {
  const verified = mode === "current";
  const historical = mode === "historical";
  const elements = new Map();
  function element(id) {
    if (!elements.has(id)) elements.set(id, {
      id, innerHTML: '', textContent: '', value: '', hidden: false, checked: true, dataset: {},
      classList: {contains: () => false, toggle() {}}, appendChild() {}, querySelector() {return null;}
    });
    return elements.get(id);
  }
  const testData = structuredClone(data);
  testData.lean_checked = verified;
  testData.source_scan = mode === "source";
  testData.has_compiled_snapshot = verified || historical;
  testData.provenance = {source: verified || historical ? 'lean' : 'source', fresh: !historical, checked_at: 'saved-check-date'};
  if (historical) {
    testData.main_path_root = 'thm:c13_patch_main';
    testData.main_path_label = '2D patch theorem';
  } else {
    delete testData.main_path_root;
    delete testData.main_path_label;
  }
  const context = {
    window: {BLUEPRINT: testData},
    document: {getElementById: element, documentElement: element('root'),
      createElement: () => ({value: '', textContent: ''}), querySelectorAll: () => [], addEventListener() {}},
    getComputedStyle: () => ({getPropertyValue: () => '#555'}),
    localStorage: {getItem: () => null, setItem() {}}, location: {hash: '#overview'},
    history: {replaceState() {}}, matchMedia: () => ({matches: false}),
  };
  vm.runInNewContext(script, context, {filename: 'dashboard-inline.js'});
  assert(element('kpis').innerHTML.includes(verified ? 'statements checked' : historical ? 'saved build' : 'unverified'));
  assert(element('evidence').innerHTML.includes(verified ? 'Current compiled Lean report' : historical ? 'Saved compiled Lean report' : 'Unverified source inventory'));
  for (const removed of ['statements corrected', 'issues flagged', 'Paper audit', 'Proof plan']) {
    assert(!element('kpis').innerHTML.includes(removed), removed);
  }
  assert(!/Paper issues|Paper audit|Proof plan|statement_fix|fixd/.test(html));
  assert(element('mainPath').textContent.includes(historical ? '2D patch theorem' : 'Front theorem'));
  assert(element('mainPath').title.includes(historical ? 'thm:c13_patch_main' : 'thm:main'));
  assert(element('nodeTable').innerHTML.includes(data.nodes[0].id));
  element('nodeSearch').value = '__no_such_node__';
  element('nodeSearch').onchange?.();
  element('nodeSearch').oninput();
  assert(!element('nodeTable').innerHTML.includes('data-open='));
}
console.log('Dashboard offline smoke checks passed.');
