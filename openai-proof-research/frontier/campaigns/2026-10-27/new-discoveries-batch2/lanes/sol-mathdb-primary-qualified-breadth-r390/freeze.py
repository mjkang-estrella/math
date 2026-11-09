import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent; R=B/'root-mathdb-breadth-intake-r389'
def ref(p):
 p=p.resolve(); b=p.read_bytes(); return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
refs={}
def add(p,expected=None):
 r=ref(p)
 if expected:
  assert r['sha256']==expected['sha256'] and r['size']==expected['size'],str(p)
 refs[r['path']]=r
for p in R.iterdir():
 if p.is_file():add(p)
for x in json.loads((R/'manifest.json').read_text())['files']:add(R/x['path'],x)
for x in json.loads((R/'bindings.json').read_text()):add(pathlib.Path(x['original']),x)
for name in ['accepted-exclusions.json','historical-dispositions.json','manifest.json','bindings.json']:
 for p in B.glob('*r304/'+name):add(p)
add(B/'root-mathdb-cayley-review-intake-r363/disposition.json')
C=B/'pi-mathdb-full-corpus-inventory-r301';add(C/'manifest.json')
m=json.loads((C/'manifest.json').read_text());print('corpus manifest type',type(m).__name__)
# Persist initial flat reference set before any scientific content is opened.
p=L/'input-bindings.json';p.write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'refs':list(refs.values())},indent=2)+'\n');p.chmod(0o444)
print('Frozen',len(refs),'flat refs')
