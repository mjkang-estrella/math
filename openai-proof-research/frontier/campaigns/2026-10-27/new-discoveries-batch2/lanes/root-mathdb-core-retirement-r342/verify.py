from pathlib import Path
import json,hashlib,sys,datetime
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,o):(R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bs=json.loads((R/'bindings.json').read_text())
for e in bs:
 for p in [Path(e['original']),R/e['copy']]:
  assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
C=R/'frozen/pi-core-containment-source-hypothesis-r341'
ms=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in ms}
for e in ms:
 p=C/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
refs=json.loads((C/'bindings.json').read_text())['bindings']
for e in refs:
 p=Path(e['original']);assert p.is_file(),str(p)
 if 'sha256' in e:assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
sources=json.loads((C/'sources/provenance.json').read_text())['retained_sources']
for e in sources:
 p=C/e['file'];assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
cov=json.loads((R/'frozen/root-mathdb-breadth-intake-r340/coverage-delta.json').read_text());assert len(cov)==333
cov['393907'].update({'disposition':'retired_public_resolution','source_scope_cleared':True,'resolution':'Fayers arXiv:1007.1071 Theorem 5.1; Vandehey arXiv:0809.2134 Theorem 2.4','review':'pi-core-containment-source-hypothesis-r341','accepted_credit':0})
res=json.loads((R/'frozen/root-mathdb-breadth-intake-r340/reserved-ids.json').read_text());assert len(res['ids'])==len(set(res['ids']))==50 and not(set(map(str,res['ids']))&set(cov))
res['lane']='pi-mathdb-primary-qualified-breadth-r343'
def payload():return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
 put('coverage-delta.json',cov);put('reserved-ids.json',res)
 put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload())]})
elif sys.argv[1]=='verify':
 assert json.loads((R/'coverage-delta.json').read_text())==cov and json.loads((R/'reserved-ids.json').read_text())==res
 own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
 for e in own:
  p=R/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
 put('verification-receipt.json',{'status':'PASS','at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bs),'child_payloads':len(ms),'upstream_hashes':sum('sha256' in e for e in refs),'upstream_unhashed_existence_only':sum('sha256' not in e for e in refs),'sources':len(sources),'root_payloads':len(own),'coverage':333,'math_replay':False})
else:raise ValueError('build or verify')
print('PASS',sys.argv[1],len(bs),'bindings',len(refs),'upstream hashes')
