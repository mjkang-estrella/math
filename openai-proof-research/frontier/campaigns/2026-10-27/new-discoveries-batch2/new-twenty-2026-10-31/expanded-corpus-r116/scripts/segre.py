from functools import lru_cache
from math import factorial
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def parts(n,hi=None):
 if not n:yield ();return
 for a in range(min(n,hi or n),1-1,-1):
  for q in parts(n-a,a):yield (a,)+q
@lru_cache(None)
def permchar(lam,mu):
 if not mu:return int(not any(lam))
 r=mu[0];v=0
 for i,a in enumerate(lam):
  if a>=r:
   b=list(lam);b[i]-=r;v+=permchar(tuple(b),mu[1:])
 return v
@lru_cache(None)
def irr(beta,mu):
 if not mu:return 1
 r=mu[0];B=set(beta);v=0
 for b in beta:
  if b>=r and b-r not in B:
   s=(-1)**sum(b-r<x<b for x in B)
   v+=s*irr(tuple(sorted((B-{b})|{b-r},reverse=True)),mu[1:])
 return v
def z(mu):
 v=1
 for a,c in Counter(mu).items():v*=a**c*factorial(c)
 return v
out={}
for n in range(2,13):
 P=list(parts(n));cs=[(-1)**(n-len(l))*factorial(len(l))//__import__('functools').reduce(lambda x,y:x*factorial(y),Counter(l).values(),1) for l in P]
 M=[[permchar(l,mu) for mu in P] for l in P]
 C=[[irr(tuple(l[i]+n-1-i if i<len(l) else n-1-i for i in range(n)),mu) for mu in P] for l in P]
 for i,c in enumerate(C):
  for j,d in enumerate(C):assert sum(Fraction(a*b,z(mu)) for a,b,mu in zip(c,d,P))==int(i==j)
 rows={}
 for t in list(range(1,13))+[16,24,32]:
  ch=[sum(c*M[i][j]**t for i,c in enumerate(cs)) for j in range(len(P))]
  mult=[sum(Fraction(a*b,z(mu)) for a,b,mu in zip(ch,c,P)) for c in C]
  assert all(x.denominator==1 and x>=0 for x in mult)
  rows[str(t)]={'support':[list(l) for l,x in zip(P,mult) if x], 'min_multiplicity':int(min(mult)),'en_coefficient':ch[P.index((n,))]*(-1)**(n-1)}
  assert rows[str(t)]['en_coefficient']==1
 base=rows['2']['support'];bad={t:[l for l in r['support'] if l not in base] for t,r in rows.items() if int(t)>=3}; print(n,len(P),len(base),{t:v for t,v in bad.items() if v},flush=True)
 out[str(n)]=rows
(D/'outputs/segre.json').write_text(json.dumps(out,indent=2)+'\n')
