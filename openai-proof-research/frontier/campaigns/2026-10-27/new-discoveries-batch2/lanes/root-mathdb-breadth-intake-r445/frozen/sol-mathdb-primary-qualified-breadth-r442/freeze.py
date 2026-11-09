from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent
refs={};checks=[]
def bind(p,h=None,s=None):
 p=p.resolve();b=p.read_bytes();d={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 if h is not None:assert d['sha256']==h and (s is None or d['size']==s),str(p)
 refs[str(p)]=d
 return b
def manifest(d,excluded):
 m=json.loads(bind(d/'manifest.json'));es=(m['files']+m.get('frozen_inputs',[])) if isinstance(m,dict) else m
 assert {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-excluded=={e['path'] for e in es},str(d)
 for e in es:bind(d/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 checks.append({'lane':d.name,'files':len(es),'excluded':sorted(excluded)})
I=L/'pi-mathdb-full-corpus-inventory-r301'
A=L/'root-mathdb-breadth-intake-r441'
manifest(A,{'manifest.json','verification-receipt.json'})
for e in json.loads((A/'bindings.json').read_text()):bind(Path(e['original']),e['sha256'],e['size'])
manifest(I,{'manifest.json','verification-receipt.json'})
for name in ['root-mathdb-coverage-reconcile-r304','root-mathdb-breadth-intake-r363']:
 d=L/name
 if not d.exists():
  ds=list(L.glob('*r'+name[-3:]));assert len(ds)==1;d=ds[0]
 manifest(d,{'manifest.json','verification-receipt.json'})
for p in [L.parent/'AGENTS.md',L.parents[4]/'AGENTS.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 if p.exists():bind(p)
(R/'bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(R/'freeze-receipt.json').write_text(json.dumps({'status':'PASS','checks':checks,'original_files':len(refs),'scientific_reading_started':False},indent=2)+'\n')
print(json.dumps(checks));print('bound',len(refs))
