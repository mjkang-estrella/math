import json,hashlib,pathlib,datetime
O=pathlib.Path(__file__).resolve().parent; L=O.parent; I=L/'root-mathdb-breadth-intake-r695'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def bind(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def check(p,e):
 b=bind(p);assert b['sha256']==e['sha256'] and b['size']==e.get('size',e.get('bytes')),(str(p),b,e);return b
rows=[bind(I/'manifest.json'),bind(I/'verification-receipt.json')];m=load(I/'manifest.json')
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|{'manifest.json','verification-receipt.json'}
for e in m['files']:rows.append(check(I/e['path'],e))
for e in load(I/'bindings.json'):
 for k in ['original','copy']:rows.append(check(pathlib.Path(e[k]),e))
inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20
for e in chunks:rows.append(check(R/e['path'],e))
assert len(inv['frozen_inputs'])==8
for e in inv['frozen_inputs']:rows.append(check(R/e['path'],e))
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md','root-mathdb-cayley-review-intake-r363/disposition.json']:
 rows.append(bind(L/rel))
for rel in ['ledger.json','prior-campaign-context.json']:rows.append(bind(L.parent/rel))
(O/'initial-bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows,'chunks':20,'frozen_inputs':8},indent=2)+'\n')
print('payload and pairs OK;20chunks OK',len(rows))
