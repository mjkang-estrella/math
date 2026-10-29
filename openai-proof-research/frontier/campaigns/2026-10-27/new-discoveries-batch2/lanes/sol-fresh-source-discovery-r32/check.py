import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(30)
from fractions import Fraction as F
from math import comb,factorial
from pathlib import Path
import json
b=Path(__file__).resolve().parent

def rising(a,k):
 v=F(1)
 for j in range(k):v*=a+j
 return v

def comps(k,n):
 if n==1:return [(k,)]
 return [(i,)+s for i in range(k+1) for s in comps(k-i,n-1)]

def add(p,s,c):p[s]=p.get(s,F(0))+c

def bep(s,a,edges):
 p={};n=len(a)
 for x,y,w in edges:
  for x,y in [(x,y),(y,x)]:
   if s[x]:
    t=list(s);t[x]-=1;t[y]+=1;add(p,tuple(t),w*s[x]*(a[x]+s[x]-1))
    add(p,s,-w*s[x]*(a[y]+s[y]))
 return {s:c for s,c in p.items() if c}
# Exact normalized-monomial identity L D_s=sum_t Q_st D_t.
identities=0;balances=0
for a,edges in [([F(1,7),F(2,3),F(3,5)],[(0,1,F(2)),(1,2,F(3,2))]),([F(1,1000)]*4,[(0,1,F(1)),(1,2,F(1)),(2,3,F(1)),(3,0,F(1))])]:
 n=len(a)
 for k in range(1,5):
  st=comps(k,n);den={s:__import__('functools').reduce(lambda x,j:x*rising(a[j],s[j]),range(n),F(1)) for s in st}
  pi={s:F(factorial(k),1)*den[s]/rising(sum(a),k)/__import__('functools').reduce(lambda x,j:x*factorial(s[j]),range(n),1) for s in st}
  assert sum(pi.values())==1
  for s in st:
   q={}
   for x,y,w in edges:
    for x,y in [(x,y),(y,x)]:
     if s[x]:
      t=list(s);t[x]-=1;t[y]+=1;t=tuple(t);v=w*s[x]*(a[y]+s[y]);add(q,t,v);add(q,s,-v)
      rev=w*t[y]*(a[x]+t[x]);assert pi[s]*v==pi[t]*rev;balances+=1
   expected={t:v/den[t] for t,v in q.items() if v}
   got={t:v/den[s] for t,v in bep(s,a,edges).items()}
   assert expected==got;identities+=1
# Q4 / C4 x C4: exact known one-particle failure consistency test.
a=F(1,1000);z=1+16*a
pi=[(1+a)/z]+[a*comb(4,r)/z for r in range(1,5)]
h=list(map(F,[0,0,1,2,3]));mean=sum(p*x for p,x in zip(pi,h));var=sum(p*(x-mean)**2 for p,x in zip(pi,h))
energy=sum(pi[r]*2*a*(4-r)*(h[r+1]-h[r])**2 for r in range(4));ray=energy/var
assert ray==56*a*(1+16*a)/(31+207*a)
assert ray<2*a
out={'status':'PASS exact auxiliary identities only; NO source resolution','normalized_monomial_identities':identities,'detailed_balance_identities':balances,'known_Q4_alpha':'1/1000','known_Q4_radial_trial':[str(x) for x in h],'rayleigh':str(ray),'one_particle_gap':str(2*a),'strict_gap':str(2*a-ray),'credit':0}
(b/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
