import pathlib,subprocess,json,hashlib,re,sys
D=pathlib.Path(__file__).resolve().parents[1]
for p in [D/'formal/Cube.lean',D/'formal/Signed.lean']:
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',p.read_text()),p
receipts=[]
for name,args in [('cube',['-o','Cube.olean','Cube.lean']),('signed',['-o','Signed.olean','Signed.lean']),('inventory',['Inventory.lean']),('audit',['Audit.lean']),('safety',['Safety.lean'])]:
 subprocess.run([sys.executable,str(D/'scripts/limited.py'),name,sys.executable,str(D/'scripts/lean.py'),*args],check=True)
 r=json.loads((D/f'logs/{name}.receipt.json').read_text());assert r['returncode']==0,(name,(D/f'logs/{name}.log').read_text());receipts.append(r)
log=(D/'logs/audit.log').read_text();assert 'sorryAx' not in log
for ax in re.findall(r'depends on axioms: \[([^]]*)\]',log):assert set(ax.split(', ')) <= {'propext','Classical.choice','Quot.sound'}
names=set(re.findall(r'^LOCAL (.+)$',(D/'logs/inventory.log').read_text(),re.M));safe=set(re.findall(r'^SAFE (.+)$',(D/'logs/safety.log').read_text(),re.M));assert names==safe and len(names)==33
(D/'replay-result.json').write_text(json.dumps({'status':'PASS','strict_warningAsError':True,'local_declarations':len(names),'all_generated_in_namespace_audited':True,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'environment':'Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612','trust_limit':'Prebuilt external dependency oleans trusted. No complete upstream rebuild or source-to-olean attestation. RSS sampling is not cgroup enforcement.','runs':receipts},indent=2)+'\n')
print('Fresh strict replay and all-local-declaration audit PASS')
