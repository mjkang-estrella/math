import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent; I=B/'root-mathdb-breadth-intake-r453'; V=B/'pi-mathdb-full-corpus-inventory-r301'
def h(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_bytes())
bind=[]
def pin(p,expected=None,size=None):
 b=p.read_bytes(); d=h(b)
 if expected:assert d==expected,(str(p),d,expected)
 if size is not None:assert len(b)==size,str(p)
 bind.append(dict(original=str(p),sha256=d,bytes=len(b)));return b
# No upstream code runs; all top-level manifest files and original bindings checked independently.
for e in load(I/'manifest.json')['files']:pin(I/e['path'],e['sha256'],e.get('size',e.get('bytes')))
for e in load(I/'bindings.json'):
 pin(pathlib.Path(e['original']),e['sha256'],e.get('size',e.get('bytes')))
 pin(pathlib.Path(e['copy']),e['sha256'],e.get('size',e.get('bytes')))
for n in ['manifest.json','bindings.json','reserved-ids.json','queue.json','coverage-delta.json']:pin(I/n)
chunks=[e for e in load(V/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:pin(V/e['path'],e['sha256'],e['bytes'])
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 D=B/name;pin(D/'manifest.json');m=load(D/'manifest.json');print(name,'manifest shape',type(m).__name__)
 es=m['files'] if isinstance(m,dict) else m
 for e in es:pin(D/e['path'],e['sha256'],e.get('size',e.get('bytes')))
# Flat refs, no nested binding expansion and no corpus copies.
bind=list({e['original']:e for e in bind}.values())
(L/'bindings.json').write_text(json.dumps(bind,indent=2)+'\n')
(L/'frozen_inputs.json').write_text(json.dumps([e['original'] for e in bind],indent=2)+'\n')
(L/'freeze-receipt.json').write_text(json.dumps(dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=len(bind),chunks=20),indent=2)+'\n')
print('PASS',len(bind),'flat inputs; twenty chunks verified')
print('queue',str(load(I/'queue.json'))[:4000]);print('coverage keys',list(load(I/'coverage-delta.json')))
