from pathlib import Path
from fractions import Fraction as F
from math import comb
import json,random,sympy as S
P=Path(__file__).resolve().parent;x=S.Symbol('x');rng=random.Random(110)
def det(a):
 a=[[F(v) for v in r] for r in a];d=F(1)
 for k in range(len(a)):
  p=next((i for i in range(k,len(a)) if a[i][k]),None)
  if p is None:return F(0)
  if p!=k:a[k],a[p]=a[p],a[k];d=-d
  v=a[k][k];d*=v
  for i in range(k+1,len(a)):
   q=a[i][k]/v
   for j in range(k+1,len(a)):a[i][j]-=q*a[k][j]
 return d
def minors(a):
 n=len(a)-1
 return [det([[a[n-1-2*j+i] if 0<=n-1-2*j+i<=n else 0 for j in range(k)] for i in range(k)]) for k in range(1,n+1)]
def hyp(a):
 p=S.Poly(sum(S.Rational(v.numerator,v.denominator)*x**i if isinstance(v,F) else v*x**i for i,v in enumerate(a)),x)
 return p.count_roots(-S.oo,0)==p.sqf_part().degree()
def quasi(a):
 if all(v==0 for v in a[1::2]):return hyp(a[::2])
 d=minors(a);m=next((i for i,v in enumerate(d) if v<=0),len(d))
 if any(v!=0 for v in d[m:]):return False
 if m==len(d):return True
 e=S.Poly(sum(v*x**i for i,v in enumerate(a[::2])),x);o=S.Poly(sum(v*x**i for i,v in enumerate(a[1::2])),x);g=S.gcd(e,o)
 return g.count_roots(-S.oo,0)==g.sqf_part().degree()
def q(k):
 l=k//2
 return [comb(l,i//2) if k%2 or i%2==0 else 0 for i in range(k+1)]
def Y(b):
 return all(quasi([b[m+i]*v for i,v in enumerate(q(k))]) for k in range(2,len(b)) for m in range(len(b)-k))
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,v in enumerate(a):
  for j,w in enumerate(b):c[i+j]+=v*w
 return c
assert minors([1,3,3,1])==[F(3),F(8),F(8)]
assert quasi([1,0,3,0,3,0,1]);assert not quasi([1]*7)
rows=[];pairs=0;eligible=0;fail=[]
for n in [6,7,8]:
 bs=[[1]*(n+1)]+[[(i+1)**r for i in range(n+1)] for r in [1,2,3]]+[[comb(n,i)**r for i in range(n+1)] for r in [1,2]]
 bs += [[rng.randint(1,12) for i in range(n+1)] for _ in range(24)]
 for b in bs:
  y=Y(b);rows.append({'n':n,'b':b,'Y':y})
  if not y:continue
  eligible+=1
  for z in range(12):
   a=[1]
   # stable rational factors, genuine degree n; exact Routh checks
   if n%2:a=mul(a,[rng.randint(1,9),rng.randint(1,9)])
   for j in range(n//2):a=mul(a,[rng.randint(1,9),rng.randint(1,9),rng.randint(1,9)])
   assert all(v>0 for v in minors(a));pairs+=1
   ds=minors([v*w for v,w in zip(a,b)])
   if not all(v>0 for v in ds):fail.append({'a':a,'b':b,'minors':list(map(str,ds))})
# a generic sign-relaxed HB pair cannot be assumed stable; exact low-order distinction
out={'seed':110,'b_candidates':len(rows),'Y_candidates':eligible,'stable_pairs':pairs,'source_counterexamples':fail,'rows':rows,'route_obstruction':{'identity_degree6':'g=1+x+...+x^6 lies in Y6 and X6, but is not quasi-stable','hurwitz_minors':list(map(str,minors([1]*7)))},'scope':'bounded exact checks only; no sufficiency proof for all b or all stable f'}
(P/'check-results.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2));assert not fail
# Exact obstruction to an unrestricted multivariate-stability-preserver reduction.
i=S.I;z=-6+i;u=6+i;w=i;v=(-4+3*i)/5
K=u*v+2*z*v+2*u*w+z*w
assert S.expand(K)==0
assert all(S.im(t)>0 for t in [z,u,w,v])
assert all(t<0 for t in [S.Rational(-1,2),S.Integer(-2)])
out['symbol_obstruction']={'H':'1+2z+2w+zw is real stable; its separately homogenized K is not','K':'uv+2zv+2uw+zw','upper_halfplane_zero':['-6+i','6+i','i','(-4+3i)/5'],'exact_zero':True,'scope':'fails a stronger proof route even for a known stable g; not a source counterexample'}
(P/'check-results.json').write_text(json.dumps(out,indent=2));print('separate-homogenization exact obstruction PASS')
