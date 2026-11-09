from fractions import Fraction as F
from functools import lru_cache
from collections import Counter,defaultdict
from math import factorial
import pathlib,json,sys
L=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]) if len(sys.argv)>1 else 17
@lru_cache(None)
def parts(n,m=100):
 if n==0:return ((),)
 return tuple((i,)+p for i in range(min(n,m),0,-1) for p in parts(n-i,i))
def z(mu):
 x=1
 for i,c in Counter(mu).items():x*=i**c*factorial(c)
 return x
def mul(a,b):
 c=defaultdict(F)
 for u,x in a.items():
  for v,y in b.items():c[tuple(sorted(u+v,reverse=True))]+=x*y
 return dict(c)
@lru_cache(None)
def pleth(i,a):
 if a==0:return {():F(1)}
 out=defaultdict(F)
 for k in range(1,a+1):
  pk={tuple(k*x for x in mu):F(1,z(mu)) for mu in parts(i)}
  for mu,v in mul(pk,pleth(i,a-k)).items():out[mu]+=v/a
 return dict(out)
@lru_cache(None)
def chi(lam,mu):
 if not mu:return int(not lam)
 k=mu[0];ell=len(lam);beta=[v+ell-1-i for i,v in enumerate(lam)];ans=0
 for b in beta:
  if b<k or b-k in beta:continue
  sign=(-1)**sum(b-k<c<b for c in beta);bb=sorted([c for c in beta if c!=b]+[b-k],reverse=True);ll=tuple(v-ell+1+i for i,v in enumerate(bb));ll=tuple(v for v in ll if v)
  ans+=sign*chi(ll,mu[1:])
 return ans
ps=parts(N);zs=[z(mu)for mu in ps];classes=[factorial(N)//x for x in zs];table=[[chi(lam,mu) for mu in ps]for lam in ps]
# Verify irreducible orthogonality before using the character table.
assert all(sum(classes[j]*c*c for j,c in enumerate(row))==factorial(N) for row in table)
dp={(0,0):{():F(1)}};out=[]
for m in range(1,N+1):
 nd={}
 for (size,blocks),poly in dp.items():
  for a in range((N-size)//m+1):
   key=(size+a*m,blocks+a);dest=nd.setdefault(key,defaultdict(F))
   for mu,v in mul(poly,pleth(m,a)).items():dest[mu]+=v
 dp=nd
 if m<2:continue
 chars=[]
 for d in range(N):
  pp=dp.get((N,N-d),{});row=[]
  for mu,zz in zip(ps,zs):
   v=pp.get(mu,0)*zz;assert v.denominator==1 if hasattr(v,'denominator') else True;row.append(int(v))
  chars.append(row)
 violations=[];minimum=None
 for d in range(1,N-1):
  diff=[chars[d][j]**2-chars[d-1][j]*chars[d+1][j] for j in range(len(ps))]
  for lam,irr in zip(ps,table):
   numerator=sum(a*b*c for a,b,c in zip(diff,irr,classes));assert numerator%factorial(N)==0;coeff=numerator//factorial(N);minimum=coeff if minimum is None else min(minimum,coeff)
   if coeff<0:violations.append({'degree':d,'partition':lam,'coefficient':coeff})
 row={'n':N,'m':m,'conjugacy_classes':len(ps),'minimum_schur_coefficient':minimum,'violations':violations};out.append(row);print(row,flush=True);(L/'outputs'/f'orbits-{N}.json').write_text(json.dumps(out,indent=2))
