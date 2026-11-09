from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent
refs={};checks=[]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def bind(p):
 p=p.resolve();e={'original':str(p),'sha256':sha(p),'size':p.stat().st_size};refs[str(p)]=e;return e
def check(p,e):
 a=bind(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes',a['size'])),str(p)
A=L/'root-mathdb-breadth-intake-r425'
for name in ['root-mathdb-breadth-intake-r425','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/name;bind(d/'manifest.json');m=json.loads((d/'manifest.json').read_text());entries=m['files'] if isinstance(m,dict) else m
 for e in entries:check(d/e['path'],e)
 checks.append({'manifest':str(d/'manifest.json'),'entries':len(entries)})
# One flat level of actual-original bindings. No recursive histories or expansion.
for e in json.loads((A/'bindings.json').read_text()):check(Path(e['original']),e)
I=L/'pi-mathdb-full-corpus-inventory-r301';bind(I/'manifest.json')
chunks=[e for e in json.loads((I/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(I/e['path'],{'sha256':e['sha256'],'size':e['bytes']})
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',Path('AGENTS.md'),Path('sources/upstream.json')]:bind(p)
(R/'bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(R/'freeze-receipt.json').write_text(json.dumps({'checks':checks,'chunks':20,'bindings':len(refs),'flat_only':True,'science_read_after_this_receipt':True},indent=2)+'\n')
print('FREEZE PASS',len(refs),checks)
