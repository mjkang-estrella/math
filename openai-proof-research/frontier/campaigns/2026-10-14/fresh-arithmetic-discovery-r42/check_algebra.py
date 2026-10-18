"""Exact finite diagnostics; not a proof of arbitrary-field descent or Ramseyness."""
from fractions import Fraction as F
from random import Random
import json

def add(p,q):
 r=p.copy()
 for k,v in q.items():r[k]=r.get(k,F(0))+v
 return {k:v for k,v in r.items() if v}
def scale(p,c):return {k:v*c for k,v in p.items() if v*c}
def mul(p,q):
 r={}
 for (i,j),v in p.items():
  for (k,l),w in q.items():r[(i+k,j+l)]=r.get((i+k,j+l),F(0))+v*w
 return {k:v for k,v in r.items() if v}
def ev(p,x,y):return sum(v*x**i*y**j for (i,j),v in p.items())
def g(left,right):
 a,b,c=left;A,B,C=right
 first=scale(mul({(0,1):F(1),(0,0):-A},{(1,0):F(1),(0,0):-c}),(B-C)*(b-a))
 second=scale(mul({(1,0):F(1),(0,0):-a},{(0,1):F(1),(0,0):-C}),-(b-c)*(B-A))
 return scale(add(first,second),1/((b-c)*(b-a)*(a-c)))
def cr(t,a,b,c):return (t-a)*(b-c)/((t-c)*(b-a))
def uncr(v,a,b,c):return (v*(b-a)*c-(b-c)*a)/(v*(b-a)-(b-c))
rng=Random(17242);checks=0
for _ in range(200):
 l=list(map(F,rng.sample(range(-30,31),3)));r=list(map(F,rng.sample(range(-30,31),3)))
 p=g(l,r)
 for a,b in zip(l,r):assert ev(p,a,b)==0;checks+=1
 assert g(l,l)=={(0,1):F(1),(1,0):F(-1)};checks+=1
 for v in map(F,range(2,12)):
  if v*(l[1]-l[0])==l[1]-l[2] or v*(r[1]-r[0])==r[1]-r[2]:continue
  x,y=uncr(v,*l),uncr(v,*r)
  assert ev(p,x,y)==0 and cr(x,*l)==cr(y,*r)==v;checks+=1
 q=g(r,l);prod=mul(p,q)
 assert max(i for i,j in prod)<=2 and max(j for i,j in prod)<=2;checks+=1
 for a,b in zip(l,r):assert ev(prod,a,b)==0 and ev(prod,b,a)==0;checks+=1
J={(2,0):F(1),(1,1):F(-2),(0,2):F(1)}
assert mul(g([F(0),F(1),F(2)],[F(0),F(1),F(2)]),g([F(3),F(4),F(5)],[F(3),F(4),F(5)]))==J
L=[[1,0,1],[1,0,-1],[0,2,0]];S=[-1,1,1];J0=[[0,0,1],[0,-2,0],[1,0,0]]
assert [[sum(L[k][i]*S[k]*L[k][j] for k in range(3)) for j in range(3)] for i in range(3)]==[[-2*v for v in row] for row in J0]
print(json.dumps({'status':'PASS','seed':17242,'cases':200,'exact_assertions':checks+2,'limits':'Finite rational diagnostics only; field-localization, annihilator descent, and universal Ramsey statement are proved in candidate.md, not established computationally.'},indent=2))
