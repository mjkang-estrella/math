from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;L=R.parent;B=L.parent
refs={}
def bind(p,expected=None):
 p=Path(p);data=p.read_bytes();e={'path':str(p),'sha256':hashlib.sha256(data).hexdigest(),'size':len(data)}
 if expected: assert e['sha256']==expected['sha256'] and e['size']==expected.get('size',expected.get('bytes')),str(p)
 refs[str(p)]=e
 return data
def load(p):return json.loads(bind(p))
I=L/'root-mathdb-breadth-intake-r413'
m=load(I/'manifest.json')
for e in m['files']:bind(I/e['path'],e)
b=load(I/'bindings.json')
for e in b:bind(e['original'],e)
# Flat references already declared by the actual child; no recursive history expansion.
c=L/'sol-mathdb-primary-qualified-breadth-r410/bindings.json'
x=load(c)
for e in x['references']:bind(e['path'],e)
C=L/'pi-mathdb-full-corpus-inventory-r301';cm=load(C/'manifest.json')
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:bind(C/e['path'],e)
for n in ['ledger.json','prior-campaign-context.json']:bind(B/n)
for p in (L/'root-mathdb-accepted-exclusions-r304').iterdir():
 if p.is_file():bind(p)
bind(L/'root-mathdb-cayley-review-intake-r363/disposition.json')
(R/'bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'policy':'flat in-place references; no source/history copies; no upstream verifier execution or receipt writer','references':list(refs.values()),'chunks':[{**e,'absolute':str(C/e['path'])} for e in chunks]},indent=2)+'\n')
print('FROZEN',len(refs),'references; 20 chunks verified in place; root manifest files verified read-only')
