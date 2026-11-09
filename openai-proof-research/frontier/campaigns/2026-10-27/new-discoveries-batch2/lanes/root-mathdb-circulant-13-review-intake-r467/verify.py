from pathlib import Path
import json,hashlib,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent
C=R/'frozen/claude-mathdb-circulant-13-certificate-review-r376'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,n):assert p.stat().st_size==n and sha(p)==h,str(p)
def put(n,x):(R/n).write_text(json.dumps(x,indent=2)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
 check(Path(e['original']),e['sha256'],e['size']);check(Path(e['copy']),e['sha256'],e['size'])
m=json.loads((C/'manifest.json').read_text())['files']
assert len(m)==46 and len({e['path'] for e in m})==46
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}=={e['path'] for e in m}|{'manifest.json','verification-receipt.json'}
for e in m:check(C/e['path'],e['sha256'],e['size'])
ib=json.loads((C/'input-bindings.json').read_text());assert ib['status']=='PASS' and not ib['failures']
assert len(ib['refs'])==82 and len(ib['r360_original_refs'])==72
for e in ib['refs']+ib['r360_original_refs']:check(Path(e['path']),e['sha256'],e['size'])
I=Path(ib['intake_dir'])
assert sha(I/'manifest.json')==ib['intake_manifest_sha256']
assert sha(I/'frozen/claude-mathdb-primary-qualified-breadth-r360/manifest.json')==ib['r360_manifest_sha256']
receipt=json.loads((C/'verification-receipt.json').read_text())
assert receipt['status']=='PASS' and receipt['failures']==[] and receipt['accepted_credit']==0
assert receipt['replay']=={'indep_exit':0,'extra_exit':0,'outputs_identical':True}
a=json.loads((C/'runs/indep_check.json').read_text())
assert a['K12']['states']==152 and a['K12']['edges']==128 and a['K12']['periods']==[12,12]
assert sorted(map(int,a['witness_words']))==[12]+list(range(142,165,2))
assert len(json.loads((R/'frozen/root-mathdb-breadth-intake-r465/coverage-delta.json').read_text()))==3033
own=lambda:{str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':put('manifest.json',{'files':[{'path':p,'size':(R/p).stat().st_size,'sha256':sha(R/p)} for p in sorted(own())]})
elif sys.argv[1]=='verify':
 es=json.loads((R/'manifest.json').read_text())['files'];assert own()=={e['path'] for e in es}
 for e in es:check(R/e['path'],e['sha256'],e['size'])
 put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'review_payloads':46,'review_input_refs':154,'independent_math_replay_by_root':False,'reviewer_replay_reported_pass':True,'coverage_unchanged':3033,'accepted_credit':0})
else:raise ValueError('mode')
print('PASS',sys.argv[1], 'review integrity; no mathematical replay by root')
