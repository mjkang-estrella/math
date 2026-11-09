import os,resource,signal
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(30,30));signal.alarm(40)
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json,random
b=Path(__file__).resolve().parent

def ev(p,x):
 r=F(0)
 for c in p[::-1]:r=r*x+c
 return r

def mul(a,c):
 p=[F(0)]*(len(a)+len(c)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(c):p[i+j]+=x*y
 return p

def add(a,c):
 p=[F(0)]*max(len(a),len(c))
 for i,x in enumerate(a):p[i]+=x
 for i,x in enumerate(c):p[i]+=x
 return p

def power(p,n):
 r=[F(1)]
 for _ in range(n):r=mul(r,p)
 return r

def bernpoly(coeff):
 n=len(coeff)-1;r=[F(0)]
 for k,c in enumerate(coeff):r=add(r,[F(0)]*k+[c*x for x in power([1,-1],n-k)])
 return r

out={'status':'PASS','limits':{'AS':536870912,'CPU':30,'wall_alarm':40,'threads':1},'checks':{}}
# Rounded Bernstein construction, independently evaluate expanded monomial polynomial
# and original Bernstein sum at rational grid points.
c=0;maxerr={}
for n in [4,8,16,24]:
 # h has integer endpoints, but rational nonintegral interior coefficients.
 h=[F(2),F(-7,3),F(4,3)]
 bs=[round(comb(n,k)*ev(h,F(k,n))) for k in range(n+1)]
 p=bernpoly(bs);assert ev(p,F(0))==2 and ev(p,F(1))==1
 me=F(0)
 for j in range(65):
  x=F(j,64)
  original=sum(F(bs[k])*x**k*(1-x)**(n-k) for k in range(n+1))
  assert original==ev(p,x)
  unrounded=sum(comb(n,k)*ev(h,F(k,n))*x**k*(1-x)**(n-k) for k in range(n+1))
  bound=F(1,2)*sum(x**k*(1-x)**(n-k) for k in range(1,n))
  assert abs(original-unrounded)<=bound
  me=max(me,abs(original-ev(h,x)));c+=1
 maxerr[str(n)]=str(me)
out['checks']['rounded_expanded_vs_bernstein']=c;out['rounding_grid_errors']=maxerr
# Exact endpoint-preserving congruence for diverse integer polynomials.
rng=random.Random(203711);c=0
for _ in range(100):
 m=[rng.choice([-5,-3,-1,1,3,5])]+[rng.randint(-4,4) for _ in range(3)]+[1]
 a=mul([0,1,-1],[rng.randint(-6,6) for _ in range(4)])
 H=[rng.randint(-6,6) for _ in range(6)]
 correction=mul(m,mul([0,1,-1],H));P=add(a,correction)
 assert ev(P,F(0))==ev(P,F(1))==0
 # Polynomial long division certifies congruence without evaluations.
 r=add(P,[-x for x in a])
 while len(r)>=len(m):
  scale=r[-1];shift=len(r)-len(m)
  for k,x in enumerate(m):r[k+shift]-=scale*x
  assert r[-1]==0;r.pop()
 assert all(x==0 for x in r);c+=1
out['checks']['endpoint_and_congruence']=c
# Positivity-to-tree coefficient bridge on a representative nontrivial P.
P=[0,0,1,-2,1] # x^2(1-x)^2
for n in range(4,30):
 bs=[sum(P[j]*comb(n-j,k-j) for j in range(min(k,len(P)-1)+1)) for k in range(n+1)]
 assert all(0<=v<=comb(n,k) for k,v in enumerate(bs))
 assert bernpoly(bs)==[F(x) for x in P]+[F(0)]*(n+1-len(P))
out['checks']['positive_tree_degrees']=26
# Contraction for non-sPV cube root of 2, with certified rational root enclosure.
l=F(1259921,1000000);u=F(1259922,1000000)
assert l**3<2<u**3
# x^2(x-1)^2 is increasing for x>1; enclosure proves 0<P(cuberoot2)<1/2.
assert 0<ev(P,l)<ev(P,u)<F(1,2)
out['checks']['exact_algebraic_contraction']={'minimal_polynomial':'x^3-2','lambda_interval':[str(l),str(u)],'P_interval':[str(ev(P,l)),str(ev(P,u))],'scope':'known instance diagnostic, no discovery credit'}
(b/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
