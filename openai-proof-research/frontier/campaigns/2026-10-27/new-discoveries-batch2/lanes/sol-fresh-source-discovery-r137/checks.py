import itertools,json
from pathlib import Path
L=Path(__file__).resolve().parent
Z=(0,)*9;I=(1,0,0,0,1,0,0,0,1)
def mul(a,b):return tuple(sum(a[3*i+k]*b[3*k+j] for k in range(3)) for i in range(3) for j in range(3))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def mod(a):return tuple(x%2 for x in a)
def rank(a):
 rows=[list(a[3*i:3*i+3]) for i in range(3)];r=0
 for c in range(3):
  p=next((i for i in range(r,3) if rows[i][c]),None)
  if p is None:continue
  rows[r],rows[p]=rows[p],rows[r]
  for i in range(3):
   if i!=r and rows[i][c]:rows[i]=[(x+y)%2 for x,y in zip(rows[i],rows[r])]
  r+=1
 return r
def rowspace(a):return {tuple(sum(v[i]*a[3*i+j] for i in range(3))%2 for j in range(3)) for v in itertools.product(range(2),repeat=3)}
allm=list(itertools.product(range(2),repeat=9))
ids=[a for a in allm if mod(mul(a,a))==a]
nils=[a for a in allm if mod(mul(mul(a,a),a))==Z]
tested=0
for e in ids:
 r=rank(e)
 for n in nils:
  a=mod(add(e,n));lo=3-rank(mod(sub(a,I)));hi=rank(a)
  assert lo<=r<=hi;tested+=1
finite_lift=0
for a in allm:
 b=mod(sub(a,mul(a,a)));sp=rowspace(b)
 feasible={rank(f) for f in ids if all(tuple(mod(sub(f,a))[3*i:3*i+3]) in sp for i in range(3))}
 expected=set(range(3-rank(mod(sub(a,I))),rank(a)+1))
 assert feasible==expected
 finite_lift+=1
e=(1,0,0,0,0,0,0,0,0);n=(0,1,0,0,0,1,0,0,0)
a=add(e,n);b=sub(a,mul(a,a));m=(0,0,0,0,-1,0,0,0,0);f=add(a,mul(m,b))
assert mul(e,e)==e and mul(mul(n,n),n)==Z and mul(f,f)==f
# Every row of B has second coordinate zero; E-A has a nonzero second coordinate.
assert all(b[3*i+1]==0 for i in range(3)) and sub(e,a)[1]!=0
j=dict(status='PASS',idempotents_F2=len(ids),nilpotents_F2=len(nils),nilclean_pair_rank_tests=tested,all_F2_matrices_rank_interval_tests=finite_lift,integer_original_idempotent_not_reachable=True,integer_alternative_exchanger={'A':a,'B':b,'M':m,'F':f},scope='Exact finite field and one integer control only; no integral lifting theorem, no source resolution')
(L/'checks.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
