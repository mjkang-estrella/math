from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent; L=R.parent; refs={}; checks=[]
def bind(p):
 p=p.resolve(); b=p.read_bytes(); refs[str(p)]={'original':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)};return b
def check(p,e):
 b=bind(p); assert hashlib.sha256(b).hexdigest()==e['sha256'] and len(b)==e.get('size',e.get('bytes',len(b))),str(p)
for name in ['root-mathdb-breadth-intake-r439','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/name;m=json.loads(bind(d/'manifest.json')); es=m if isinstance(m,list) else m['files'];
 for e in es: check(d/e['path'],e)
 checks.append({'lane':name,'manifest_entries_validated':len(es)})
 if name=='root-mathdb-breadth-intake-r439':
  for e in json.loads(bind(d/'bindings.json')):check(Path(e['original']),e)
# Explicit required administrative originals, no recursive binding expansion.
for p in [L/'root-mathdb-breadth-intake-r439'/n for n in ['queue.json','reserved-ids.json','coverage-delta.json']]:bind(p)
for p in [L/'root-mathdb-accepted-exclusions-r304'/n for n in ['accepted-exclusions.json','historical-dispositions.json']]:bind(p)
for p in [L/'root-mathdb-cayley-review-intake-r363'/n for n in ['disposition.json','reserved-ids.json']]:bind(p)
I=L/'pi-mathdb-full-corpus-inventory-r301'; chunks=[e for e in json.loads((I/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
(R/'bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(R/'preflight.json').write_text(json.dumps({'ok':True,'checks':checks,'chunks':20,'flat_originals':len(refs)},indent=2)+'\n')
print((R/'preflight.json').read_text())
