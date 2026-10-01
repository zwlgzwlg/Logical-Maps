// NODE_PATH=/path/to/node_modules node scripts/check_model_verdicts_ui.cjs
// A model's page sorts every principle by what the model says about it:
// satisfied, violated, or not settled. A model records a few properties and
// the rest follow, so the derived verdicts wait behind a closed disclosure.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {JSDOM,VirtualConsole}=require('jsdom');
const root=path.resolve(__dirname,'..');
const template=fs.readFileSync(path.join(root,'viewer/template.html'),'utf8');
const cert={source_id:'paper',lean:'none',produced_by:'Fixture',checked_by:[]};
// The model itself is Lean-checked; the results that derive from it are not.
const leanCert={...cert,lean:'verified',lean_ref:'Fixture.model'};
const rule=(id,premises,conclusion)=>({id,premises,conclusion,status:'proved',certificate:cert,sources:['Fixture'],source_names:['Fixture']});
// A holds and B fails by record. C follows from A, so it holds; D would force
// B, so it fails. Nothing touches E.
const data={topic:{id:'verdicts',title:'Verdict fixture',background:[],source_catalog:[{id:'paper',name:'Paper',kind:'published-paper'}]},
  principles:['a','b','c','d','e'].map(id=>({id,name:id.toUpperCase(),statement:'Statement of '+id.toUpperCase()})),
  results:[rule('ac',['a'],'c'),rule('db',['d'],'b')],
  models:[{id:'m',name:'Fixture model',status:'proved',satisfies:['a'],violates:['b'],certificate:leanCert,sources:['Fixture'],source_names:['Fixture']}]};
const errors=[],vc=new VirtualConsole();vc.on('jsdomError',e=>errors.push(e));
const dom=new JSDOM(template.replace('/*__PMAP_DATA__*/null',JSON.stringify(data)),
  {url:'https://maps.example/',runScripts:'dangerously',pretendToBeVisual:true,virtualConsole:vc});
const w=dom.window,d=w.document;
try{
  w.eval('openPage({type:"model", id:"m"})');
  const page=d.getElementById('page');
  assert.equal(page.querySelector('h1').textContent,'Fixture model');

  // The three groups, named and counted, in the order a reader asks about.
  const heads=[...page.querySelectorAll('h3.verdict-group')];
  assert.deepEqual(heads.map(h=>h.firstChild.textContent.trim()),['Satisfied','Violated','Unknown'],'Three groups, verdict first');
  assert.deepEqual(heads.map(h=>h.querySelector('.n').textContent),['2','2','1'],'Each counts everything it covers, shown or not');

  // Everything between one heading and the next belongs to that group.
  const section=head=>{const out=[];let n=head.nextElementSibling;
    while(n&&!['H2','H3'].includes(n.tagName)){out.push(n);n=n.nextElementSibling;}return out;};
  const named=el=>[...el.querySelectorAll('tr')].map(tr=>tr.querySelector('[data-principle]')?.dataset.principle);
  const groups=Object.fromEntries(heads.map(h=>{
    const parts=section(h), details=parts.find(x=>x.tagName==='DETAILS');
    return [h.firstChild.textContent.trim(),
      {listed:parts.filter(x=>x.tagName==='TABLE').flatMap(named), details, hidden:details?named(details):[]}];
  }));
  assert.deepEqual(groups.Satisfied.listed,['a'],'The recorded verdict is listed');
  assert.deepEqual(groups.Satisfied.hidden,['c'],'The derived one waits behind the disclosure');
  assert.deepEqual(groups.Violated.listed,['b']);
  assert.deepEqual(groups.Violated.hidden,['d']);
  assert.deepEqual(groups.Unknown.listed,['e'],'Nothing is derived about a principle the model leaves open');
  assert.equal(groups.Unknown.details,undefined,'So that group has no disclosure');
  assert.equal([...page.querySelectorAll('.verdict-table tr')].length,data.principles.length,'Every principle appears exactly once');

  // Closed by default, and the rows are inside it, which is what makes the
  // browser hide them; jsdom lays nothing out, so the structure is the contract.
  for (const key of ['Satisfied','Violated']) {
    assert.equal(groups[key].details.open,false,`The ${key.toLowerCase()} disclosure starts closed`);
    assert.equal(groups[key].details.firstElementChild.tagName,'SUMMARY');
    assert.match(groups[key].details.querySelector('summary').textContent,/^1 more, derived/,'And says how many it holds');
  }

  // The principle is the left column; the evidence sits to its right and keeps
  // its route to the derivation.
  const row=id=>page.querySelector(`[data-principle="${id}"]`).closest('tr');
  assert.equal(row('a').firstElementChild.querySelector('[data-principle]').dataset.principle,'a','The name leads the row');
  const evidence=id=>row(id).querySelector('.verdict-cell [data-verdict]');
  assert.equal(evidence('a').dataset.verdictModel,'m','A recorded verdict still links to its evidence');
  assert.equal(evidence('c').dataset.verdict,'c','And so does a derived one');
  assert.equal(row('e').querySelector('[data-verdict]'),null,'An unsettled principle has no evidence to link to');

  // One line per principle: the names column shrinks to its widest name so the
  // evidence starts just past it rather than at the far edge, and the evidence
  // is text rather than a bordered button. jsdom lays nothing out, so this
  // pins the rules to the markup rather than measuring the result.
  const style=el=>w.getComputedStyle(el);
  assert.equal(style(row('a').firstElementChild).width,'1%','The names column takes only what it needs');
  assert.equal(style(row('a').firstElementChild).whiteSpace,'nowrap','Keeping each name on one line');
  assert.equal(style(row('a').firstElementChild).borderBottomWidth,'0px','No rule between rows to space them apart');
  assert.equal(style(evidence('a')).padding,'0px','And the evidence carries no button chrome');
  assert.equal(style(evidence('a').querySelector('.badge.source')).whiteSpace,'nowrap','A source badge stays on one line');

  // The group heading carries the verdict, so the rows under it do not repeat
  // the mark; what is left to report is the derivation and the sources.
  assert.equal(evidence('a').querySelector('.model-flag').textContent,'','A recorded row adds no mark of its own');
  assert.equal(evidence('c').querySelector('.model-flag').textContent,'derived','A derived row says only that');
  assert.ok(evidence('a').querySelector('.badge.source'),'Both still carry their sources');
  assert.ok(evidence('c').querySelector('.badge.source'));

  // A verdict is Lean-checked only when everything under it is. The model is,
  // so its recorded verdicts are; the results deriving the rest are not, so
  // those are not.
  assert.ok(evidence('a').querySelector('.badge.lean.verified'),'A recorded verdict of a Lean-checked model says so');
  assert.ok(evidence('b').querySelector('.badge.lean.verified'),'Either way round');
  assert.equal(evidence('c').querySelector('.badge.lean.verified'),null,'A verdict derived through an unverified result does not');

  // And the one-line answer at the foot of the graph's details pane carries it
  // beside the witness it names.
  d.querySelector('.tab[data-tab="graph"]').click();
  w.eval('select({type:"principle", id:"a"})');
  const foot=d.getElementById('graph-details-foot');
  assert.match(foot.textContent,/Consistent with the background \(Fixture model\)/,'The foot names the witness');
  assert.ok(foot.querySelector('.badge.lean.verified'),'And says it is Lean-checked');
  w.eval('select(null)');
  assert.equal(foot.hidden,true);
  w.eval('openPage({type:"model", id:"m"})');

  // The mark stays where no heading gives it: the theory explorer's own list.
  d.querySelector('.tab[data-tab="models"]').click();
  w.eval('select({type:"model", id:"m"})');
  const explorer=d.querySelector('#model-principles [data-assumption-row="a"] [data-verdict]');
  assert.equal(explorer.querySelector('.model-flag').textContent,'✓','The explorer still shows the verdict itself');

  assert.deepEqual(errors.map(String),[]);
}finally{w.close();}

// A model written as a definition and arguments, as the build exports it: the
// flattened lists beside the arguments, and a generated conjectured companion.
const argCert={...cert,date:'2026-01-01',produced_by:'Author'};
const args=[{holds:['a'],text:'Why A holds.'},{fails:['b'],text:'First reason B fails.',id:'first'},
  {fails:['b'],writeup:'b-writeup',by:'Later author',date:'2026-02-01',revisions:[{date:'2026-02-02',note:'Tidied.'}]},
  {holds:['e'],standing:'conjectured',tier:'bronze',text:'Why E might hold.',companion_id:'n-conj',date:'2026-01-20'}];
const flat={id:'n',name:'Argument model',status:'proved',satisfies:['a'],violates:['b'],certificate:argCert,sources:['Fixture'],source_names:['Fixture'],
  definition:'What the model is.',arguments:args,notes:'Miscellany.',history:[{date:'2026-01-15',by:'Old',summary:'An old change.',satisfies:['a']}]};
const companion={id:'n-conj',name:'Argument model',status:'conjectured',tier:'bronze',satisfies:['a','e'],violates:['b'],certificate:argCert,sources:['Fixture'],source_names:['Fixture'],
  definition:'What the model is.',arguments:[args[3]],notes:'Why E might hold.',companion_of:'n',model_check:{model:'n',satisfies:['e'],violates:[]}};
const data2={...data,models:[flat,companion]};
const errors2=[],vc2=new VirtualConsole();vc2.on('jsdomError',e=>errors2.push(e));
const dom2=new JSDOM(template.replace('/*__PMAP_DATA__*/null',JSON.stringify(data2)),
  {url:'https://maps.example/',runScripts:'dangerously',pretendToBeVisual:true,virtualConsole:vc2});
const w2=dom2.window,d2=w2.document;
try{
  w2.eval('openPage({type:"model", id:"n"})');
  const page=d2.getElementById('page');
  const h2s=[...page.querySelectorAll('h2')].map(h=>h.textContent);
  assert.ok(h2s.includes('Definition')&&page.textContent.includes('What the model is.'),'The definition comes first');
  assert.ok(h2s.indexOf('Definition')<h2s.indexOf('Principles'));
  const row=id=>page.querySelector(`.verdict-table [data-principle="${id}"]`).closest('tr');
  const routes=id=>[...row(id).querySelectorAll('details.argument')];
  assert.equal(routes('a').length,1,'A recorded verdict lists its argument');
  assert.equal(routes('b').length,2,'Two routes to one verdict are both shown');
  assert.match(routes('b')[1].querySelector('summary').textContent,/write-up · Later author, 2026-02-01/,'Each route says what kind of reason it is, and whose');
  assert.match(routes('b')[0].textContent,/n#first/,'An argument with an id shows its address');
  assert.equal(routes('b')[1].querySelector('a').getAttribute('href'),'writeups/b-writeup.html');
  assert.match(routes('b')[1].textContent,/Revised 2026-02-02: Tidied\./);
  assert.equal(routes('c').length,0,'A derived verdict has no arguments of its own');
  assert.ok(row('c').closest('details.derived-verdicts'),'And stays behind the disclosure');
  assert.equal(routes('e').length,1,'A conjectured verdict is unknown, with its conjectured argument');
  assert.ok(routes('e')[0].querySelector('.badge.conj'));
  assert.equal(routes('d').length,0);
  assert.equal([...page.querySelectorAll('.verdict-table tr')].length,data.principles.length,'Still one row per principle');
  assert.ok(h2s.includes('Notes')&&h2s.includes('History'));
  assert.match(page.textContent,/An old change\./);

  w2.eval('openPage({type:"model-verdict", id:"n", principle:"b"})');
  assert.match(page.textContent,/recorded directly for the model, by the arguments below/);
  assert.equal(page.querySelectorAll('details.argument').length,2);

  w2.eval('openPage({type:"model", id:"n-conj"})');
  assert.ok(page.querySelector('.record-summary [data-open-model="n"]'),'A companion names the model it conjectures about');
  assert.match(page.querySelector('dl').textContent,/conjectured by.*Author, 2026-01-20.*model.*Argument model/,'And who proposed its arguments, not the model\'s certificate');
  assert.ok(![...page.querySelectorAll('h2')].some(h=>h.textContent==='Notes'),'Its notes are its arguments, shown once');
  args[3].id='guess';w2.eval(`byMid.get('n-conj').arguments[0].id='guess';openPage({type:"model", id:"n-conj"})`);
  assert.match(page.textContent,/n#guess/,'Its arguments keep the address they have in the model');

  // The Changes tab keeps the logged history, and an argument added since it is a change of its own.
  w2.eval('state.search="";renderResults()');
  const changes=[...d2.querySelectorAll('#results tr')].map(tr=>tr.textContent);
  assert.ok(changes.some(x=>x.includes('An old change.')),'History entries are changes');
  assert.ok(changes.some(x=>x.includes('Argument added.')&&x.includes('2026-02-01')),'A later argument is one');
  assert.ok(changes.some(x=>x.includes('Tidied.')),'And so is its revision');
  assert.ok(!changes.some(x=>x.includes('Why A holds')),'An argument as old as the record is not');
  assert.ok(changes.some(x=>x.includes('Conjectured argument added: Why E might hold.')),'A later conjectured argument is a change too');
  companion.arguments[0].revisions=[{date:'2026-03-01',note:'Conjecture restated.'}];
  w2.eval(`byMid.get('n-conj').arguments[0].revisions=[{date:'2026-03-01',note:'Conjecture restated.'}];renderResults()`);
  const rows=[...d2.querySelectorAll('#results tr')];
  assert.ok(rows.some(tr=>tr.dataset.id==='n-conj'&&tr.textContent.includes('Conjecture restated.')),'A companion\'s changes are its arguments\' revisions');
  assert.ok(rows.some(tr=>tr.dataset.id==='n-conj'&&tr.textContent.includes('2026-01-20')&&!tr.classList.contains('revision')),'And it is dated by its latest argument, not by the model');
  assert.deepEqual(errors2.map(String),[]);
  console.log('PASS: a model page sorts every principle into satisfied, violated and unsettled, counts each group, leads each row with the principle, keeps the route to the evidence, holds the derived verdicts in a closed disclosure, keeps each row to a single line while the ungrouped explorer list keeps its marks; a model written as arguments shows its definition, then each recorded or conjectured verdict with its arguments, derived verdicts without, its history, and its companion.');
}finally{w2.close();}
