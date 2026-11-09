from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent.parent; O=Path(__file__).resolve().parent; I=L/'root-mathdb-breadth-intake-r541'
def J(p):return json.loads(p.read_text())
def ent(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=ent(p); assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
refs={}
def bind(p):refs[str(p)]=ent(p)
bind(I/'manifest.json');assert refs[str(I/'manifest.json')]['sha256']=='cb5a7055f1988395c09ac7deedcbedd7830ec5af2fb21b242ed8cfc45579f7a0'
m=J(I/'manifest.json');expected={e['path'] for e in m['files']}|set(m['excluded_exact_paths']);assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected
for e in m['files']:check(I/e['path'],e);bind(I/e['path'])
bind(I/'verification-receipt.json')
for e in J(I/'bindings.json'):
 for k in ['original','copy']:check(Path(e[k]),e);bind(Path(e[k]))
R=L/'pi-mathdb-full-corpus-inventory-r301';check(R/'manifest.json',next(e for e in m['files'] if e['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'));bind(R/'manifest.json')
r=J(R/'manifest.json');print('inventory keys',r.keys())
for e in r['files']:
 if e['path'].startswith('corpus/'):check(R/e['path'],e);bind(R/e['path'])
print('frozen_inputs',r.get('frozen_inputs'))
for e in r.get('frozen_inputs',[]):
 print(e)
 p=Path(e.get('path',e.get('original','')));p=p if p.is_absolute() else R/p;check(p,e);bind(p)
# Bind administrative/prior references before their content is read.
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-breadth-intake-r304'/'accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304'/'historical-dispositions.json']:
 if p.exists():bind(p)
for p in L.glob('*r363/*'):
 if p.is_file():bind(p)
(O/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
for name in ['coverage-delta.json','reserved-ids.json','active-breadth-reservations.json','adjudications.json','hypothesis-queue.json']:
 x=J(I/name);print(name, str(x)[:11000] if name not in ['coverage-delta.json'] else [(k,type(v).__name__,len(v) if hasattr(v,'__len__') else v) for k,v in x.items()])
print('bound',len(refs),'chunks',sum('/corpus/' in p for p in refs))
