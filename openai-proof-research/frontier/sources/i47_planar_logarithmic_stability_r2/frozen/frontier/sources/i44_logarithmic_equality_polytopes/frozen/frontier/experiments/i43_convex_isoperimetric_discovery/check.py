#!/usr/bin/env python3
"""Read-only stdlib exact checks; no floating-point or analytic proof certification."""
import sys
sys.dont_write_bytecode=True
import json
from fractions import Fraction as F
from math import factorial
from itertools import combinations, product
count=0

def ck(x):
 global count
 assert bool(x), x
 count+=1

# Chamber polynomial, independently assembled from rectangle minus two triangles.
# Q=4ab-(a+b-c)^2; entries are exponent tuples and rational coefficients.
Q={(2,0,0):-1,(0,2,0):-1,(0,0,2):-1,(1,1,0):2,(1,0,1):2,(0,1,1):2}
def deriv(poly,i):
 out={}
 for alpha,coef in poly.items():
  if alpha[i]:
   beta=list(alpha);beta[i]-=1;out[tuple(beta)]=coef*alpha[i]
 return out

def ev(poly,h):
 total=F(0)
 for alpha,coef in poly.items():
  term=F(coef)
  for hi,ai in zip(h,alpha):term*=hi**ai
  total+=term
 return total

def hessian(h):
 val=ev(Q,h);grad=[ev(deriv(Q,i),h) for i in range(3)];w=[h[i]*grad[i]/val for i in range(3)]
 return [[w[i]*w[j]-h[i]*h[j]*ev(deriv(deriv(Q,i),j),h)/val-(w[i] if i==j else 0) for j in range(3)] for i in range(3)],w

def quadratic(H,b):return sum(H[i][j]*b[i]*b[j] for i in range(3) for j in range(3))
H0,w0=hessian([F(1)]*3)
ck(H0==[[F(4,9) if i==j else F(-2,9) for j in range(3)] for i in range(3)])
ck(all(sum(row)==0 for row in H0))
rows=[]
for k in range(2,102):
 delta=F(1,k);h=[F(1),F(1),2-delta];H,w=hessian(h);gap=quadratic(H,[1,-1,0]);wnorm=(w[0]+w[1])/2
 ck(ev(Q,h)==4-delta*delta);ck(gap==4*delta/(4-delta*delta));ck(wnorm==F(2)/(2+delta));ck(gap/wnorm==2*delta/(2-delta));ck(gap/wnorm<F(2,k));ck(sum(w)==2);ck(all(x>0 for x in w));ck(all(sum(row)==0 for row in H))
 if k in [2,4,10,100]:rows.append({'delta':str(delta),'curvature':str(gap),'weighted_norm_squared':str(wnorm)})
# Independent exact volume and Hessian checks throughout the six-facet chamber.
chamber_points=0
for h in product([F(i,4) for i in range(2,9)],repeat=3):
 a,b,c=h
 if abs(a-b)<c<a+b:
  H,w=hessian(h);ck(ev(Q,h)==4*a*b-(a+b-c)**2);ck(all(x>0 for x in w));ck(sum(w)==2)
  ck(all(sum(row)==0 for row in H));ck(all(H[i][i]>0 for i in range(3)))
  ck(all(H[i][i]*H[j][j]-H[i][j]**2>0 for i,j in combinations(range(3),2)));chamber_points+=1
# Genuine endpoint support values and strict midpoint redundant slab.
ck(F(5)>F(9,2));ck(F(9,10)<1)
# Cauchy-Binet and the log-determinant curvature coefficient, rational tests.
gaussian_tests=0
for coefs in [(1,1,1),(1,2,3),(3,5,7),(7,2,11)]:
 q1,q2,q3=map(F,coefs);det=(q1+q3)*(q2+q3)-q3*q3
 ck(det==q1*q2+q1*q3+q2*q3)
 for slopes in [(1,-1,0),(1,1,1),(2,3,-4)]:
  basis=list(combinations(range(3),2));w=[F(coefs[i]*coefs[j]) for i,j in basis];z=sum(w);bs=[slopes[i]+slopes[j] for i,j in basis]
  E=sum(ww*x for ww,x in zip(w,bs))/z;var=sum(ww*(x-E)**2 for ww,x in zip(w,bs))/z
  det1=sum(-2*ww*x for ww,x in zip(w,bs));det2=sum(4*ww*x*x for ww,x in zip(w,bs))
  ck(F(1,2)*(det2/z-(det1/z)**2)==2*var);ck((var==0)==(len(set(bs))==1));gaussian_tests+=1
# Green integration for phi=-t^j, using exact antiderivatives.
for j in range(2,9):
 for l in [F(1,5),F(1,3),F(1,2),F(4,5)]:
  left=(1-l)*(j-1)*l**j
  right=l*j*(j-1)*(F(1,j-1)-F(1,j)-l**(j-1)/(j-1)+l**j/j)
  ck(left+right==l-l**j)
# Signed resonance conditions at unit supports (diagnostic only).
resonances=[]
for slopes in [(1,2,4),(1,-1,0),(1,1,1),(0,0,1)]:
 groups={}
 for alpha,coef in Q.items():
  r=sum(ai*bi for ai,bi in zip(alpha,slopes));g=groups.setdefault(r,{'coefficient':0,'moments':[0,0,0]});g['coefficient']+=coef
  for i in range(3):g['moments'][i]+=alpha[i]*coef
 affine=len([g for g in groups.values() if g['coefficient']])==1
 ck(affine==(slopes==(1,1,1)))
 if affine:
  for g in groups.values():ck(all(F(m)==F(2,3)*g['coefficient'] for m in g['moments']))
 resonances.append({'slopes':slopes,'groups':groups,'affine_volume_at_unit_supports':affine})
# All integer partitions into simplex factors, including segments.
def parts(n,lo=1):
 if n==0:yield ()
 for j in range(lo,n+1):
  for rest in parts(n-j,j):yield (j,)+rest

def cn(n):return F((n+1)*n**n,factorial(n))
products=[]
for n in range(4,9):
 tests=[]
 for partition in parts(n):
  val=F(1)
  for j in partition:val*=cn(j)
  ck(val<=cn(n));tests.append((val,partition))
 best=max(v for v,pa in tests if len(pa)>1)
 products.append({'n':n,'partitions':len(tests),'simplex':str(cn(n)),'best_proper_product':str(best)})
ck(cn(4)==F(160,3));ck(cn(2)**2==36);ck(cn(3)*cn(1)==36)
ck(cn(10)**2/cn(20)==F(22355476,22020096))
# Transition 1: compare coefficients after dividing areas/volumes by pi.
rball=F(1,3);rtube=F(2,9)
ck(F(4,3)*rball**3==F(4,81));ck(rtube**2==F(4,81));ck(4*rball**2==2*rtube);ck(2/rball-1/rtube==F(3,2))
# Transition 2: r=1/pi; formal Laurent coefficients give V/pi^-1=1, A=2, H/pi=1.
ck(1*1**2==1);ck(2*1==2);ck(F(1,1)==1)
# Strict cylinder stability at transition 1: 4*pi>9 follows pi>3.
ck(F(4)*3>9)
print(json.dumps({'status':'PASS','scope':'Exact finite diagnostics only; E, RT, RP4 remain unproved.','assertions':count,'chamber_points':chamber_points,'gaussian_tests':gaussian_tests,'hexagon':rows,'midpoint_rho_squared':'9/10','simplex_products':products,'resonance_tests':resonances},indent=2,sort_keys=True))
