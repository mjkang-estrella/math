from pathlib import Path
from math import comb
import hashlib,json,runpy
D=Path(__file__).resolve().parent
S=D.parent/'sol-hankel-breadth-depth-r1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p.relative_to(S)):sha(p) for p in S.rglob('*') if p.is_file()}
M=json.loads((S/'manifest.json').read_text())
assert set(before)-set(M['excluded'])==set(M['files'])
for f,h in M['files'].items():assert before[f]==h,f
bindings=0
for name in ['inputs-index.json','retrieved-freeze.json']:
 for row in json.loads((S/name).read_text()):
  assert sha(Path(row['original']))==sha(S/row['copy'])==row['sha256']
  bindings+=1
result=runpy.run_path(str(S/'checks.py'))['run']()
assert result==json.loads((S/'check-results.json').read_text())
def C(n,k):return comb(n,k) if 0<=k<=n else 0
def P(k,r,i):return C(k,i)*C(k+r+i-1,i)
linear=tel=0
for r in range(1,17):
 for k in range(17):
  for i in range(7):
   for j in range(7):
    assert P(k,r,i)*P(k,r,j)==sum(C(l,i)*C(l,j)*C(r+i+j-1,i+j-l)*P(k,r,l) for l in range(max(i,j),i+j+1)),(r,k,i,j)
    linear+=1
 for n in range(1,25):
  for l in range(n+2):
   assert sum((2*k+r)*P(k,r,l) for k in range(n))==(n+r-1)*C(n,l+1)*C(n+r+l-1,l),(r,n,l)
   tel+=1
after={str(p.relative_to(S)):sha(p) for p in S.rglob('*') if p.is_file()}
assert before==after
out={'status':'PASS','predecessor_manifest':len(M['files']),'bindings':bindings,'predecessor_checks':result,'linearization_controls':linear,'telescoping_controls':tel,'limit':'Finite controls and integrity only; universal proof and eligibility pending.'}
(D/'receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
