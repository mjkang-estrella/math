from pathlib import Path
import json,hashlib,datetime
from fractions import Fraction
from math import factorial
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in manifest and 'verification-receipt.json' not in manifest
assert set(manifest)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
for name,digest in manifest.items():assert h(L/name)==digest,name
prov=json.loads((L/'provenance.json').read_text())
for r in prov['freeze_bindings']:
 assert h(L/r['copy'])==r['sha256']
 if not r['administrative']:assert h(Path(r['original']))==r['sha256']
for p,digest in prov['scientific_hashes'].items():assert h(L/p)==digest
assert h(Path(prov['helper_guard']['path']))==prov['helper_guard']['sha256']
c=json.loads((L/'certificate-results.json').read_text());edges=c['edges'];assert len(set(tuple(sorted(e)) for e in edges))==19
reached={0}
for _ in range(10):reached|={x for a,b in edges for x,y in [(a,b),(b,a)] if y in reached}
assert len(reached)==10
dist=[2**s.bit_count()*3**(10-s.bit_count()) for s in range(1024)]
coeff=[]
updates=[]
for s in range(1024):
 row=[]
 for v in range(10):
  nei=[a+b-v for a,b in edges if v in (a,b)];vote=sum(1 if s&(1<<j) else -1 for j in nei)
  row.append(s|(1<<v) if vote>0 else s&~(1<<v) if vote<0 else s)
 updates.append(row)
for k in range(241):
 nd=[0]*1024
 for s in range(1024):
  for z in updates[s]:nd[z]+=dist[s]
 assert sum(dist)==5**10*10**k
 x=sum(a for s,a in enumerate(nd) if s&2)-10*sum(a for s,a in enumerate(dist) if s&2)
 assert x==int(c['coefficients'][k]);coeff.append(x);dist=nd
A=sum(8**k*(factorial(240)//factorial(k))*x for k,x in enumerate(coeff));B=sum(80**k*(factorial(240)//factorial(k)) for k in range(241));C=121*80**241;D=19521;W=5**10
assert {key:str(val) for key,val in dict(A=A,B=B,C=C,D=D,W=W).items()}==c['integer_certificate']
assert 10**6*(D*A-W*C)>18*W*(D*B+C)
assert 10**6*(D*A+W*C)<19*W*D*B
for name,digest in manifest.items():assert h(L/name)==digest,name
for r in prov['freeze_bindings']:
 if not r['administrative']:assert h(Path(r['original']))==r['sha256']
receipt=dict(passed=True,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(L/'manifest.json'),files_verified=len(manifest),scientific_originals_and_copies_before_after=True,exact_forward_coefficients_verified=241,strict_integer_bounds_verified=True,counts_unchanged=[9,39,40],independent_acceptance_review=False)
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
