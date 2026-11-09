from pathlib import Path
import json,hashlib,re,subprocess,os,collections
r=Path(__file__).resolve().parents[1]
replay=json.loads((r/'fresh-extracted/logs/replay.json').read_text())
assert replay['status']=='PASS PARTIAL r5q PACKET ONLY'
mods=json.loads((r/'modules.json').read_text()); receipts=replay['receipts']
assert len(receipts)==2*len(mods)+8
assert all(x['cap_reason'] is None for x in receipts)
assert all(x['exit']==0 for x in receipts[:2*len(mods)])
assert all(x['exit']!=0 for x in receipts[2*len(mods):])
audit=(r/'fresh-extracted/logs/strict-AuditR5.log').read_text()
count=int(re.search(r'LOCAL_TOTAL (\d+)',audit).group(1))
assert len([x for x in audit.splitlines() if 'MODULE ' in x and ' DECL ' in x])==count
assert 'FLAGS unsafe=true' not in audit and 'partial=true' not in audit and 'axiom=true' not in audit
for m in mods:
 assert (r/'formal'/(m+'.lean')).read_bytes()==(r/'fresh-extracted/formal'/(m+'.lean')).read_bytes()
rows=json.loads((r/'inputs-before.json').read_text())
for x in rows:
 assert hashlib.sha256(Path(x['source']).read_bytes()).hexdigest()==x['sha256']
 assert hashlib.sha256((r/x['copy']).read_bytes()).hexdigest()==x['sha256']
(r/'inputs-after.json').write_text(json.dumps(rows,indent=2)+'\n')
for p in (r/'inputs/nut-formal-r4b/formal').glob('*.lean'):
 assert p.read_bytes()==(r/'formal'/p.name).read_bytes()
assert (r/'formal/NutInterface.lean').read_bytes()==(r/'inputs/nut-interface-r5/NutInterface.lean').read_bytes()
with (r/'logs/negative-existing-olean.log').open('w') as f:
 rc=subprocess.run(['/usr/bin/python3','-I',str(r/'fresh-extracted/replay.py')],stdout=f,stderr=subprocess.STDOUT).returncode
assert rc!=0 and 'Refusing existing oleans' in (r/'logs/negative-existing-olean.log').read_text()
by_module=collections.Counter()
for line in audit.splitlines():
 if 'MODULE ' in line and ' DECL ' in line:
  by_module[line.split('MODULE ',1)[1].split(' DECL ',1)[0]]+=1
(r/'audit-declaration-counts.json').write_text(json.dumps(dict(by_module),indent=2)+'\n')
wall=sum(x['wall_seconds'] for x in receipts);peak=max(x['peak_private_bytes'] for x in receipts)
res={'365943':{'status':'partial_zero_credit','required_endpoint':'per_support : Nut8.PerSupport','endpoint_exists':False,'endpoints':[], 'exact_statement':'∀ code ∈ Nut8.GraphClosure7_000.targets, ∀ (C : Nut8.QuotientMatrix) (s : ℤ), Nut8.Structural C s → Nut8.SupportCode C code → ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0)', 'proved_helpers':['Nut8.unsignedPatterns_complete','Nut8.catalogue_ordered_tree','Nut8.ordered_switch_exists','Nut8.catalogue_normalization'],'declaration_counts':{'all_local_including_generated':count,'strictly_compiled_modules':len(mods),'per_module':'audit-declaration-counts.json'},'completed':['B3 universal unsigned augmentation enumeration and completeness','B4 checked ordered parent data for all 194 supports and structural positive-tree normalization'],'missing':['signed enumeration and exact image membership','kernel transport of r2 normalization to the fixed catalogue or regenerated certificates','9140 remaining determinant/cofactor records','PerSupport composition'],'diagnostic_counts':{'supports':194,'unsigned_patterns':669,'normalized_signed_matrices':9172,'r2_set_equality_after_permutation_and_switch':True,'formal_count_theorem':False},'kernel_certificate_records':32,'replay':{'status':replay['status'],'calls':len(receipts),'wall_seconds_sum':wall,'peak_sampled_private_bytes':peak,'audit':'fresh-extracted/logs/strict-AuditR5.log','receipts':'fresh-extracted/logs/replay.json','negative_lean_controls':8,'existing_olean_refusal':True,'proof_sources_match_final_packet':True},'input_files':len(rows),'inputs_unchanged':True,'inherited_lean_modules_byte_identical':True,'root_interface_byte_identical':True,'source_packet':'nut-r5q-source.zip','self_accepted':False}}
(r/'results.json').write_text(json.dumps(res,indent=2)+'\n')
s=(r/'SUMMARY.md').read_text()
s+='''
The final fresh-extracted, sanitized strict replay passed for all %d modules,
with separate leanchecker calls and an audit of %d local declarations including
generated ones. All bodies, full types, module names, unsafe/partial/axiom flags
and transitive axioms are logged. Only propext, Classical.choice and Quot.sound
occur. Eight Lean negative controls were rejected, and existing-olean refusal
passed. The %d capped calls totalled %.2f process wall seconds; peak sampled
private memory was %s bytes. Audit and receipts are under fresh-extracted/logs.

All %d assigned input files are hash-bound before/after and copied with hash
identity. Every inherited Lean source and NutInterface.lean remain byte-identical.
All delivered proof sources match the fresh extraction. Every failed development
log is retained under a unique name. No child agents, git commands, shared ledger
edits, outside-lane writes, network requests, browser tabs, external messages or
publication were used. No background jobs remain at handback. Source-only packet:
nut-r5q-source.zip. Root alone adjudicates acceptance; this is zero credit.
'''%(len(mods),count,len(receipts),wall,f'{peak:,}',len(rows))
(r/'SUMMARY.md').write_text(s)
print(json.dumps({'modules':len(mods),'declarations':count,'calls':len(receipts),'wall':wall,'peak':peak}))
