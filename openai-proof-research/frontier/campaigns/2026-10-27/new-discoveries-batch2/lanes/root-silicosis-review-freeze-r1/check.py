import json,hashlib,datetime,itertools
from pathlib import Path
P=Path(__file__).resolve().parent;src=P.parent/'sol-fresh-source-discovery-r76'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
prov=json.loads((src/'provenance.json').read_text())
bad=[v['file'] for v in prov['manifest'] if sha(src/v['file'])!=v['sha256']]
assert not bad,bad
frozen={str(f.relative_to(src)):sha(f) for f in sorted(src.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 return c
def variations(a):
 signs=[1 if x>0 else -1 for x in a if x]
 return sum(x!=y for x,y in zip(signs,signs[1:]))
count=0
for n in range(5):
 for ds in itertools.product((1,2),repeat=n):
  for cs in itertools.product((-1,0,1),repeat=n+1):
   q=[0]*(n+1)
   for i,c in enumerate(cs):
    basis=[0]*i+[c]
    for d in ds[i:]:basis=mul(basis,[d,1])
    q=[a+b for a,b in zip(q,basis)]
   recur=[cs[0]]
   for d,c in zip(ds,cs[1:]):
    recur=mul(recur,[d,1]);recur[-1]+=c
   assert q==recur
   assert variations(q)<=variations(cs)
   count+=1
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
(P/'review-freeze.json').write_text(json.dumps({'utc':stamp,'source_lane':str(src),'files':frozen},indent=2)+'\n')
(P/'root-check.json').write_text(json.dumps({'utc':stamp,'status':'PASS','exact_finite_transform_cases':count,'manifest_verified':len(prov['manifest']),'frozen_files':len(frozen),'scope':'Direct rational-basis expansion versus recurrence and finite sign variations. Independent corroboration, not an analytic proof or eligibility clearance.'},indent=2)+'\n')
print(count,len(frozen))
