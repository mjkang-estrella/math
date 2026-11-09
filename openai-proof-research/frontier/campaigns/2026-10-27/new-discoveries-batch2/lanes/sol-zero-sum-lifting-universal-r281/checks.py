from pathlib import Path
from itertools import product
from itertools import combinations
import json,math
L=Path(__file__).resolve().parent
def analyze(name,A,p):
 n=len(A);r=len(A[0]);M=1<<n
 sums=[(0,)*r]*M;zero=[];F=[[0]*M for _ in range(r)];D=[0]*M
 for m in range(M):
  if m:
   bit=m&-m;i=bit.bit_length()-1;sums[m]=tuple(x+y for x,y in zip(sums[m^bit],A[i]))
  if all(x%p==0 for x in sums[m]):
   D[m]=1
   for j in range(r):F[j][m]=(sums[m][j]//p)%p
   if m:zero.append(m)
 # Explicit sparse row dependency, no lift search.
 basis={};cert=None
 for m in zero:
  row=[(m>>i)&1 for i in range(n)]+[(-sums[m][j]//p)%p for j in range(r)];dep={m:1}
  for k in sorted(basis):
   if row[k]:
    c=row[k];v,d=basis[k];row=[(x-c*y)%p for x,y in zip(row,v)]
    for t,z in d.items():
     dep[t]=(dep.get(t,0)-c*z)%p
     if not dep[t]:del dep[t]
  k=next((i for i,x in enumerate(row[:n]) if x),None)
  if k is None:
   if any(row[n:]):cert={'rows':sorted(dep.items()),'rhs':row[n:]};break
  else:
   c=pow(row[k],-1,p);basis[k]=([(x*c)%p for x in row],{t:z*c%p for t,z in dep.items()})
 if cert:
  assert all(sum(c*((m>>i)&1) for m,c in cert['rows'])%p==0 for i in range(n))
  assert [sum(c*(-sums[m][j]//p) for m,c in cert['rows'])%p for j in range(r)]==cert['rhs']
 # Unique multilinear Boolean polynomial coefficients via Mobius transform.
 def mob(v):
  v=v[:]
  for i in range(n):
   for m in range(M):
    if m>>i&1:v[m]=(v[m]-v[m^(1<<i)])%p
  return v
 coeff=[mob(v) for v in F];dc=mob(D)
 deg=lambda v:max((m.bit_count() for m,x in enumerate(v) if x),default=-1)
 # F_j=indicator*carry_j; compare with degree bound for indicator*x_i.
 high=max(((j,m,x) for j,v in enumerate(coeff) for m,x in enumerate(v) if x and m.bit_count()>r*(p-1)+1),key=lambda z:z[1].bit_count(),default=None)
 poly=None
 if high:
  j,T,c=high;S=(M-1)^T
  weights=[(m,(-1)**m.bit_count()%p) for m in zero if m&S==S]
  assert all(sum(c*((m>>i)&1) for m,c in weights)%p==0 for i in range(n))
  val=sum(c*(sums[m][j]//p) for m,c in weights)%p;assert val
  poly={'coordinate':j,'coefficient_mask':T,'coefficient':c,'multiplier_mask':S,'number_rows':len(weights),'carry_pairing':val}
 return {'name':name,'p':p,'r':r,'A':A,'zero_subsets':len(zero),'incidence_certificate':cert,'indicator_degree':deg(dc),'carry_indicator_degrees':[deg(v) for v in coeff],'polynomial_certificate':poly}
E=[]
for j in range(3):
 for a in [1,1,2,2]:E.append(tuple(a if k==j else 0 for k in range(3)))
P=[a for a in product(range(3),repeat=3) if any(a) and next(x for x in a if x)==1]
cases=[('signed-extremal',E,3),('signed-plus-mixed',E+[(1,1,1)],3),('projective-plane',P,3),('projective-plane-sign-switched',[tuple((-x)%3 for x in a) if i%2 else a for i,a in enumerate(P)],3)]
out=[analyze(*x) for x in cases]
# Control: actual signed integer lifts of E are bad against EVERY subset.
lifts=[tuple(-1 if x==2 else x for x in a) for a in E]
for m in range(1,1<<len(E)):
 s=[sum(lifts[i][j] for i in range(len(E)) if m>>i&1) for j in range(3)]
 assert not all(x%3==0 for x in s) or all(x%9==0 for x in s)
(L/'diagnostics.json').write_text(json.dumps(out,indent=2))
cap=[(1,x,y,(x*x+y*y)%3) for x,y in product(range(3),repeat=2)]
cap=[a for a in cap for _ in range(2)][:-1]
assert len(cap)==17
counts={}
for k in range(1,7):
 counts[k]=sum(all(sum(cap[i][j] for i in I)%3==0 for j in range(4)) for I in combinations(range(17),k))
assert all(counts[k]==0 for k in [1,2,3]) and counts[6]>0
(L/'composite-short-block-obstruction.json').write_text(json.dumps({'p':3,'r':4,'N':17,'A':cap,'residue_zero_counts_through_length_6':counts,'claim':'No residue-zero subset of size <=p; does not refute full packing lemma or Question 3.1.'},indent=2))
for d in out:print(d['name'],'zero',d['zero_subsets'],'incidence support',len(d['incidence_certificate']['rows']) if d['incidence_certificate'] else None,'degrees',d['carry_indicator_degrees'],'poly',d['polynomial_certificate'])
for x in json.loads((L/'cached-body-screen.json').read_text()):
 if x['hits']:print('SCREEN',x['path'],[(h['term'],h['excerpt'][:300]) for h in x['hits'][:2]])
