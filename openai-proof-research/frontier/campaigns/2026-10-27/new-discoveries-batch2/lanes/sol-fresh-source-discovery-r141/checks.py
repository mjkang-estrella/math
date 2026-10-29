import json,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
def deg(a):return a.bit_length()-1
def mul(a,b):
 c=0
 while b:
  if b&1:c^=a
  a<<=1;b>>=1
 return c
def div(a,b):
 q=0
 while a and deg(a)>=deg(b):
  k=deg(a)-deg(b);q^=1<<k;a^=b<<k
 return q,a
def gcd(a,b):
 while b:a,b=b,div(a,b)[1]
 return a
def f(a):return mul(mul(a,a),a)^a^2
def irreducible(a):
 m=deg(a);x=2;h=x
 for k in range(1,m+1):
  h=div(mul(h,h),a)[1]
  if k<=m//2 and gcd(h^x,a)!=1:return False
 return h==div(x,a)[1]
primes=[a for m in range(1,14) for a in range(1<<m,1<<(m+1)) if irreducible(a)]
def factor(a):
 out={}
 for p in primes:
  if 2*deg(p)>deg(a):break
  while div(a,p)[1]==0:
   out[p]=out.get(p,0)+1;a=div(a,p)[0]
 if a!=1:out[a]=out.get(a,0)+1
 return out
rows=[];collision_examples=[];identities=0
for n in range(1,10):
 facts={};lcm=1;alpha={};beta={};owners={}
 for q in range(1<<n,1<<(n+1)):
  a=f(q);fac=factor(a);rec=1
  for p,e in fac.items():
   for _ in range(e):rec=mul(rec,p)
   alpha[p]=alpha.get(p,0)+e;beta[p]=max(beta.get(p,0),e);owners.setdefault(p,[]).append(q)
  assert rec==a
  lcm=mul(div(lcm,gcd(lcm,a))[0],a)
 assert deg(lcm)==sum(deg(p)*e for p,e in beta.items())
 S=[p for p,v in owners.items() if deg(p)>n and len(v)>1]
 D=sum((alpha[p]-beta[p])*deg(p) for p in S)
 pair_count=sum(len(owners[p])*(len(owners[p])-1)//2 for p in S)
 for p in S:
  qs=owners[p]
  for i,q in enumerate(qs):
   for r in qs[:i]:
    h=q^r
    assert deg(h)<n and div(f(h),p)[1]==0
    assert div(mul(q,q)^mul(h,q)^mul(h,h)^1,p)[1]==0
    identities+=1
    if len(collision_examples)<12:collision_examples.append(dict(n=n,P=p,Q=q,R=r,H=h))
 rows.append(dict(n=n,values=1<<n,lcm_degree=deg(lcm),predicted_scale=2*n*(1<<n),S=len(S),large_collision_degree=D,unordered_collision_pairs=pair_count,rad_degree=sum(deg(p) for p in beta)))
# Independent direct polynomial identity for all Q,R of degree at most 7.
controls=0
for q in range(256):
 for r in range(256):
  h=q^r;g=mul(q,q)^mul(h,q)^mul(h,h)^1
  assert f(q)^f(r)==mul(h,g)
  assert f(q)^f(h)==mul(q^h,g)
  controls+=1
out=dict(status='PASS',rows=rows,collision_examples=collision_examples,large_prime_pair_checks=identities,polynomial_identity_controls=controls,independent_lcm_vs_factor_degree=True,limit='finite diagnostic for one non-special cubic only; no asymptotic or full-source proof')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
