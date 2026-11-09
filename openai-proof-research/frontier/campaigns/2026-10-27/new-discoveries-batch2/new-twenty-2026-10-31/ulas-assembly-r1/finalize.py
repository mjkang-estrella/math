from pathlib import Path
import json,hashlib,re,zipfile
L=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((L/'merge-manifest.json').read_text())
modules=manifest['union']; modules['src/UlasFinal5.lean']=dict(sha256=H((L/'merged/src/UlasFinal5.lean').read_bytes()),origins=['new assembly'])
for n,r in modules.items():
 assert H((L/'merged'/n).read_bytes())==r['sha256']
 assert (L/'fresh-replay'/n).read_bytes()==(L/'merged'/n).read_bytes()
a=json.loads((L/'fresh-replay/logs/audit-summary.json').read_text())
order=json.loads((L/'module-order.json').read_text())
for m in order:
 for phase in ['build','checker']:assert (L/'fresh-replay/logs'/f'{phase}-{m}.done').exists()
assert a['audited_equals_import_closure']
assert set(a['endpoint_axioms']['Ulas.Final5.full_theorem_E2'])=={'propext','Classical.choice','Quot.sound'}
controls=[]
for f in sorted((L/'fresh-replay/scripts').glob('*.lean')):
 if 'Negative' not in f.name and not f.name.startswith('negative-'):continue
 logs=list((L/'fresh-replay/logs').glob('negative-'+f.stem+'-*.result.json'));assert logs
 r=json.loads(logs[-1].read_text());assert r['exit_code']!=0
 out=logs[-1].with_name(logs[-1].name.replace('.result.json','.log')).read_text()
 assert 'type mismatch' in out.lower()
 controls.append(dict(source=str(f.relative_to(L)),result='rejected with type mismatch',exit_code=r['exit_code']))
assert len(controls)==11
closure=set();mods={}
for f in (L/'fresh-replay/logs').glob('declarations-*.jsonl'):
 for line in f.open():
  r=json.loads(line)
  if 'module_record' in r:mods[r['module_record']]=r
stack=['UlasFinal5']
while stack:
 n=stack.pop()
 if n in closure:continue
 closure.add(n);stack.extend(mods[n]['imports'])
assert not any('Negative' in n or n.startswith('negative-') for n in closure)
assert 'UlasFinal' in closure
metadata_defs=['EvenFormula','OddOneBound','OddThreeBound','OddOneEquality','OddThreeEquality','FifteenBound','NeverFifteen','Conj61','Conj61Some']
found={}
for f in (L/'fresh-replay/logs').glob('declarations-*.jsonl'):
 for line in f.open():
  r=json.loads(line)
  if r.get('name') in ['Ulas.'+n for n in metadata_defs]:
   assert r['module']=='UlasFinal';found[r['name']]=r['module']
assert len(found)==len(metadata_defs)
logs=[]
for tree in ['merged/logs','fresh-replay/logs']:
 for f in sorted((L/tree).glob('*.result.json')):
  r=json.loads(f.read_text());stderr=f.with_name(f.name.replace('.result.json','.stderr')).read_text()
  rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',stderr)
  logs.append(dict(path=str(f.relative_to(L)),**r,max_rss_kib=int(rss[1]) if rss else None))
result=dict(lane='ulas-assembly-r1',mathdb_id=342364,status='IMPLEMENTATION_COMPLETE_NOT_ACCEPTANCE',self_accepted=False,credit=0,root_decides=True,
 input_archives={'ulas-formal-r5a/ulas-source.zip':'9cadc73d99896766bba141fc4a67c8477f664e51647ea2af61f1c5e52b94ef18','ulas-formal-r5b/ulas-source.zip':'488e13fc75c95f1ebf0dbe4757548d5850c6fd062ae4c0ef48f63893ed7d890b'},
 merge=dict(packet_lean_counts=[32,42],shared_count=21,shared_byte_identical=True,conflicts=0,inherited_union_lean_files=53,source_modules=43,controls=11),modules=modules,
 archive=dict(path='ulas-source.zip',sha256=H((L/'ulas-source.zip').read_bytes()),safe_paths=True,source_only=True,fresh_extraction_matches=True),
 endpoints={'Ulas.Final5.full_theorem_E2':'Ulas.EvenFormula ∧ Ulas.OddOneBound ∧ Ulas.OddThreeBound ∧ Ulas.OddOneEquality ∧ Ulas.OddThreeEquality ∧ Ulas.FifteenBound ∧ Ulas.NeverFifteen','Ulas.Final5.mathdb_342364':'¬ Ulas.Conj61','Ulas.Final5.conj61_some':'Ulas.Conj61Some'},endpoint_hypotheses=0,endpoint_axioms={k:v for k,v in a['endpoint_axioms'].items() if k.startswith('Ulas.Final5.')},frozen_definition_origins=found,
 validation=dict(merged_strict_rebuild=True,fresh_extracted_strict_serial_rebuild=True,leanchecker_modules=len(order),controls=controls,negative_controls_in_endpoint_closure=False),
 audit={k:v for k,v in a.items() if k not in ['local_axioms','endpoint_axioms']},
 audit_logs='fresh-replay/logs',process_logs=logs,toolchain=dict(lean='4.34.1',mathlib='d13f23b723b8a846827a245b89c10fc7d3f11612'),
 limitations=['Explicit sufficient equality sets, not iff characterizations; NeverFifteen is universal.','No new prior-art investigation or acceptance; root decides.','Round 1 REMAINING.md was absent; the six Props are in its frozen UlasFinal.lean.','Packet summaries predate their archives; archive counts independently verified.'],
 discipline=dict(child_agents=0,git=False,network=False,external_messages=False,browser_tabs=False,writes_outside_lane=False,one_heavy_process_at_a_time=True,background_jobs_left=0))
(L/'results.json').write_text(json.dumps(result,indent=2))
(L/'SUMMARY.md').write_text(f'''# MathDB 342364 final assembly handback

Implementation complete; NOT acceptance. Root decides. No credit claimed.

UlasFinal5.lean proves Ulas.Final5.full_theorem_E2, Ulas.Final5.mathdb_342364 and Ulas.Final5.conj61_some unconditionally. All three use exactly propext, Classical.choice and Quot.sound. The full theorem combines the proved even formula and five proved odd Props through the frozen Ulas.full_theorem, including NeverFifteen. No inherited module was edited.

Both packet SHA-256 values match the brief. Their 21 shared Lean files are byte-identical; the union contains 53 inherited Lean files (42 src modules and 11 controls). One new mathematical module gives 43 src modules. Hashes and packet origins are in results.json and merge-manifest.json.

The merged tree and a fresh extraction both passed strict serial rebuilding. All 43 fresh modules passed leanchecker. All 11 inherited negative controls were rejected with type mismatch. No negative-control module enters the endpoint import closure.

The full closure audit covers {a['modules']:,} modules and {a['audited_declarations']:,} kernel declarations, including generated declarations and opaque bodies; the audited set equals the closure. LOCAL: {a['LOCAL']['declarations']:,} declarations, zero unsafe, partial, axiom, _unsafe_rec, implemented_by or extern flags, and only the three permitted transitive axioms. Upstream metadata and unrelated upstream axioms are separately inventoried. Frozen statement definitions are confirmed to originate in UlasFinal.

Source archive: ulas-source.zip, SHA-256 {result['archive']['sha256']}. REPRODUCE.md and scripts/replay.py provide resumable serial replay. Full build, checker, audit and control logs are retained under merged/logs and fresh-replay/logs.

Statement fidelity: P1 is refuted; P2 is proved. The equality families are sufficient infinite sets, not iff descriptions; the never family is universal. See STATEMENT-CORRESPONDENCE.md for the literal quantifiers, colour convention and nonzero clauses. This assembly supplies no new novelty clearance or acceptance. Round 1 REMAINING.md is absent, and the historical packet summaries have stale module counts; the frozen sources and supplied archive hashes were used.

No child agents, git, network, shared edits, external messages, publication, uploads or browser tabs. All writes and temporary/cache paths stayed in this lane. No background job remains.
''')
print(json.dumps(dict(archive=result['archive'],audit=result['audit']['LOCAL'],controls=len(controls),processes=len(logs)),indent=2))
