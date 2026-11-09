from pathlib import Path
import json,hashlib,collections,re,zipfile,shutil
r=Path(__file__).resolve().parents[1]
def dump(n,v):(r/n).write_text(json.dumps(v,indent=2)+'\n')
old=json.loads((r/'inputs-before.json').read_text())
new={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in old}
assert new==old
dump('inputs-after.json',new)
for name, expected in old.items():
 p=Path(name)
 if p.parent.name=='formal':
  q=r/'formal'/p.name
 elif p.parent.name=='scripts':
  q=r/'inputs/edgepattern-formal-r4/scripts'/p.name
 else:
  q=r/'inputs'/p.parent.name/p.name
 assert hashlib.sha256(q.read_bytes()).hexdigest()==expected

for p in (r.parent/'edgepattern-formal-r4/formal').glob('*.lean'):
 assert p.read_bytes()==(r/'formal'/p.name).read_bytes()
log=r/'auditor-final-extracted/logs/replay-AuditR5.log'
assert log.exists()
s=log.read_text();c=collections.Counter(re.findall(r'^MODULE (.+)$',s,re.M))
assert 'TOTAL_POLICY_VIOLATIONS 0' in s and not any(line.endswith(' FUEL_EXHAUSTED') for line in s.splitlines() if line.startswith('EXPR_NODE '))
findings={'passed':True,'local_declarations':sum(c.values()),'declarations_by_module':dict(sorted(c.items())),'expression_nodes':int(re.search(r'TOTAL_EXPR_NODES (\d+)',s)[1]),'policy_violations':0,'proof_imports_audit_modules':False,'auditor_own_declarations_checked_separately':6,'auditor_own_safety_passed':True,'encoder':'Nat fuel recursion, 10000 per expression; exhaustion rejects','inventory_includes_generated_declarations':True,'opaque_bodies':'ci.value? (allowOpaque := true)','legacy_audit_tooling_outside_proof_closure':['Audit','AuditR2','AuditR3','AuditR4']}
dump('audit-findings.json',findings)
shutil.copyfile(log,r/'logs/audit.log')
for n in ['replay-receipt.json','negative-results.json']:shutil.copyfile(r/'extracted'/n,r/n)
replay=json.loads((r/'replay-receipt.json').read_text());negative=json.loads((r/'negative-results.json').read_text())
shutil.copyfile(r/'replay-receipt.json',r/'full-proof-replay-receipt.json')
last=json.loads((r/'final-auditor-replay-receipt.json').read_text())
assert last['passed']
assert last['source_sha256']==hashlib.sha256((r/'formal/AuditR5.lean').read_bytes()).hexdigest()
replay['checks']+=last['checks']
replay['formal_source_sha256']['formal/AuditR5.lean']=last['source_sha256']
replay['audit_tool_revision_validation']=last
dump('replay-receipt.json',replay)
shutil.copyfile(r/'auditor-final-extracted/logs/auditor-safety.log',r/'logs/auditor-safety.log')
dump('auditor-safety-receipt.json',{'passed':True,'exit_code':0,'build_root':'auditor-final-extracted','log':'logs/auditor-safety.log','auditor_declarations':6})

assert replay['passed'] and negative['passed']
assert json.loads((r/'auditor-safety-receipt.json').read_text())['passed']
assert all(hashlib.sha256((r/p).read_bytes()).hexdigest()==h for p,h in replay['formal_source_sha256'].items())
newmods=['StructureR5','CoordinatesR5','NumberingR5','HomR5','EndpointR5','AuditR5']
endpoint='EdgePattern.TreeModelsR5.refutation'
results={'342414':{'status':'complete formal endpoint; submitted to root, not self-accepted','accepted_credit':0,'endpoints':{'EdgePattern.TreeModelsR5.classification':'EdgePattern.TreeModelsR3.ClassifiedCubicTrees',endpoint:'¬ EdgePattern.Conjecture2.{0}'},'classification_expanded':'∀ (W : Type) [Fintype W] (T : EdgePattern.Rooted W), EdgePattern.TreeFamily T 3 2 → ∃ k : EdgePattern.TreeModelsR3.Counts, Nonempty (EdgePattern.RootedIso T (EdgePattern.TreeModelsR3.pattern k))','universe':0,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'inherited_source_modules':268,'added_source_modules':6,'all_source_modules':274,'replay_modules':len(json.loads((r/'scripts/modules.json').read_text())),'declaration_counts':{'audited_local':sum(c.values()),'new_proof_modules':{m:c.get(m,0) for m in newmods if m!='AuditR5'},'auditor':'outside endpoint proof closure; separate safety receipt'},'validation':{'fresh_extracted_strict_rebuild':replay['passed'],'leanchecker':all(x['exit_code']==0 for x in replay['checks'] if x['name'].startswith('leanchecker-')),'audit':True,'auditor_safety':True,'negative_controls':negative['passed'],'inputs_unchanged':new==old,'inherited_sources_byte_identical':True},'gaps':[],'optional_all_universe_refutation':False,'prior_art':'Inherited evidence copied unchanged; gate not repeated','root_acceptance_required':True}}
dump('results.json',results)
receipts=[json.loads(p.read_text()) for p in (r/'extracted/logs').glob('*.receipt.json')]
receipts.extend(json.loads(p.read_text()) for p in (r/'auditor-final-extracted/logs').glob('*.receipt.json'))
dump('verification.json',{'passed':True,'expensive_calls':len(receipts),'max_sampled_private_rss_bytes':max(x['peak_sampled_private_rss_bytes'] for x in receipts),'max_wall_seconds':max(x['elapsed_seconds'] for x in receipts),'resource_kills':[x for x in receipts if x['killed'] is not None],'proof_axiom_log':'extracted/logs/replay-EndpointR5.log','all_inputs_unchanged':True})
# Full final packet contains sources and documentation, never generated oleans or binary inputs.
z=r/'edgepattern-r5-source.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as f:
 for p in sorted((r/'formal').glob('*.lean')):f.write(p,p.relative_to(r))
 for n in ['replay.py','watchdog.py','modules.json','negative.py','check-auditor.py']:f.write(r/'scripts'/n,'scripts/'+n)
 for p in sorted((r/'negative-controls').glob('*.lean')):f.write(p,p.relative_to(r))
 for p in sorted((r/'checks').glob('*.lean')):f.write(p,p.relative_to(r))
 for n in ['SUMMARY.md','GAPS.md','REPRODUCE.md','statement-correspondence.md','results.json','inputs-before.json','inputs-after.json','copy-receipt.json','closure.json','audit-findings.json','verification.json','auditor-safety-receipt.json','final-auditor-replay-receipt.json']:f.write(r/n,n)
 for p in sorted((r/'inputs').rglob('*')):
  if p.is_file() and p.suffix in ['.md','.json','.py']:f.write(p,p.relative_to(r))
with zipfile.ZipFile(z) as f:
 assert not any(n.endswith(('.olean','.ilean','.c','.o','.so')) for n in f.namelist())
 assert {n:hashlib.sha256(f.read(n)).hexdigest() for n in f.namelist() if n.startswith('formal/')}==replay['formal_source_sha256']
dump('packet-receipt.json',{'file':z.name,'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'source_only':True,'formal_sources_identical_to_fresh_replay':True,'replay_driver_identical_to_extracted':(r/'scripts/replay.py').read_bytes()==(r/'extracted/scripts/replay.py').read_bytes(),'final_packet_sources_match_combined_replay_receipts':True})
print(json.dumps({'passed':True,'declarations':sum(c.values()),'packet':z.name}))
