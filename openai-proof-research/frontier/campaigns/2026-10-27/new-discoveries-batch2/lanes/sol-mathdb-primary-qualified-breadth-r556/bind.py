import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parent.parent; O=pathlib.Path(__file__).resolve().parent; I=L/'root-mathdb-breadth-intake-r555'
def load(p):return json.loads(p.read_text())
def fp(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 f=fp(p);assert f['sha256']==e['sha256'] and f['size']==e.get('size',e.get('bytes')),str(p);return f
refs={}
def add(p,e=None):
 f=check(p,e) if e else fp(p);refs[str(p)]=f
# Bind all intake bytes before inspecting any admin executable/summary.
add(I/'manifest.json');add(I/'verification-receipt.json')
m=load(I/'manifest.json'); expected={e['path'] for e in m['files']}
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|set(m['excluded_exact_paths'])
for e in m['files']:add(I/e['path'],e)
for e in load(I/'bindings.json'):
 add(pathlib.Path(e['original']),e);add(pathlib.Path(e['copy']),e)
inv=L/'pi-mathdb-full-corpus-inventory-r301/manifest.json';add(inv,fp(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
j=load(inv)
print('INVENTORY KEYS',j.keys())
for k,v in j.items():
 if isinstance(v,list):print(k,len(v),str(v[:1])[:1800])
(O/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
print('BOUND',len(refs))
chunks=[e for e in j['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(j['frozen_inputs'])==8
for e in chunks+j['frozen_inputs']:add(inv.parent/e['path'],e)
B=L.parent
for p in [B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'sources/upstream.json']:
 if p.exists():add(p)
for lane in L.glob('*r304'):
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  if (lane/n).exists():add(lane/n)
for lane in L.glob('*r363'):
 for p in lane.iterdir():
  if p.is_file():add(p)
add(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(O/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(O/'binding-receipt.json').write_text(json.dumps({'integrity':'PASS','original_chunks':20,'frozen_inputs':8,'flat_references':len(refs),'upstream_code_executed':False},indent=2)+'\n')
print('COMPLETE',len(refs))
