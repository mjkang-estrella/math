from pathlib import Path
import re,json,subprocess,shutil
R=Path(__file__).resolve().parent;D=R/'replay';log=(D/'Audit.log').read_text();inv=(D/'Inventory.log').read_text()
ns=re.findall(r'^INVENTORY\|([^|]+)\|(Definitions|Witness)\|false$',inv,re.M)
assert len(ns)==87 and 'TOTAL|87' in inv
assert len(re.findall(r'^TYPE\|',inv,re.M))==87 and '⋯' not in inv
blocks=re.split(r'(?=^DECL\|)',log,flags=re.M);blocks=[b for b in blocks if b.startswith('DECL|')]
def strengthened(s):
 bs=[b for b in re.split(r'(?=^DECL\|)',s,flags=re.M) if b.startswith('DECL|')]
 names=[re.match(r'DECL\|([^|]+)\|',b)[1] for b in bs]
 assert len(names)==len(set(names))==87 and set(names)=={n for n,_ in ns}
 for name,b in zip(names,bs):
  assert re.search(r'^'+re.escape(name)+r'(?:\s|\.)',b,re.M),name
  assert '⋯' not in b
 return True
assert strengthened(log)
# No inherited type truncations; independent inventory types retained verbatim.
mutations={
 'unsafe':log.replace('UNSAFE|false','UNSAFE|true',1),
 'custom_axiom':log.replace('depends on axioms: [propext]','depends on axioms: [Evil.fake]',1),
 'partial':log.replace('Lean.DefinitionSafety.safe','Lean.DefinitionSafety.partial',1),
 'missing_axiom_report':re.sub(r"^'[^']+' (?:depends on axioms:.*|does not depend on any axioms)\n",'',log,count=1,flags=re.M),
 'missing_whole_declaration':''.join(blocks[1:]),
 'missing_type':re.sub(r'^Cayley.Contains \(p w : List.\{0\} Nat\) : Prop\n','',log,count=1,flags=re.M),
 'duplicate_declaration':log+blocks[0],
 'ellipsis':log+'\n⋯\n'}
T=R/'auditor-tests';T.mkdir(exist_ok=True)
for n in ['audit_verify.py','source-manifest.json','Definitions.lean','Witness.lean','Audit.lean','lean_guard.py','verify_pins.py','pins.json','run.sh','Definitions.log','Witness.log','Definitions.guard.json','Witness.guard.json','Audit.guard.json']:
 shutil.copyfile(D/n,T/n)
out=[]
for name,s in mutations.items():
 (T/'Audit.log').write_text(s)
 p=subprocess.run(['python3','-B',str(T/'audit_verify.py')],capture_output=True,text=True)
 (T/(name+'.stdout')).write_text(p.stdout);(T/(name+'.stderr')).write_text(p.stderr)
 try:strengthened(s);supp=True
 except AssertionError:supp=False
 out.append({'mutation':name,'candidate_accepts':p.returncode==0,'candidate_exit':p.returncode,'supplemental_coverage_accepts':supp})
assert all(not x['candidate_accepts'] for x in out if x['mutation'] in ['unsafe','custom_axiom','partial','missing_axiom_report','ellipsis'])
assert all(not x['supplemental_coverage_accepts'] for x in out if x['mutation'] in ['missing_whole_declaration','missing_type','duplicate_declaration','ellipsis'])
# Retain the mutated audit as a test fixture, never as replay evidence.
(R/'auditor-tests.json').write_text(json.dumps(out,indent=2)+'\n')
(R/'audit-review.json').write_text(json.dumps({'status':'PASS_with_supplement','independent_inventory_count':len(ns),'unique_declarations':87,'full_type_reports':87,'notes':'Candidate parser lacks independent inventory/count/type presence and uniqueness checks; supplemental coverage closes these gaps for the actual clean fresh log. This is not a proof of arbitrary parser soundness.'},indent=2)+'\n')
print('PASS actual 87-declaration inventory/types; mutation results retained')
