from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent
I=R.parent/'root-mathdb-cayley-formal-intake-r357'; C=I/'frozen/sol-mathdb-cayley-source-formal-r353'
def entry(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
def check(e,key='path'):
 p=Path(e[key]);assert entry(p)['sha256']==e['sha256'] and p.stat().st_size==e['size'],str(p)
refs={str(p):entry(p) for p in I.rglob('*') if p.is_file()}
for e in json.loads((I/'bindings.json').read_text()):
 check(e,'original');p=I/e['copy'];assert entry(p)['sha256']==e['sha256'] and p.stat().st_size==e['size'];refs[e['original']]=entry(Path(e['original']))
for f in ['input-bindings.json','administrative-bindings.json','audit-tool-binding.json']:
 x=json.loads((C/f).read_text());x=x if isinstance(x,list) else [x]
 for e in x:check(e);refs[e['path']]=e
m=json.loads((I/'manifest.json').read_text())['files']
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in m}
for e in m:check(dict(e,path=str(I/e['path'])))
m=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}==set(m)
for n,e in m.items():check(dict(e,path=str(C/n)))
(R/'freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bindings':list(refs.values()),'intake_payloads':len(json.loads((I/'manifest.json').read_text())['files']),'candidate_payloads':len(m),'status':'PASS'},indent=2)+'\n')
print('PASS freeze',len(refs),'flat originals and intake files')
