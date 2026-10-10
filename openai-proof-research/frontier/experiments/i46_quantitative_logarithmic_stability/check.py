#!/usr/bin/env python3
"""Read-only exact diagnostics; not a certificate of the analytic proof."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
VENDOR=Path(__file__).resolve().parents[3]/"frontier/sources/i46_quantitative_logarithmic_stability/vendor"
sys.path[:0]=[str(p) for p in sorted(VENDOR.glob("*.whl"))]
import sympy as s,json,itertools
count=0

def ck(x):
 global count
 assert x
 count+=1

def psd(A):
 A=s.Matrix(A)
 ck(A==A.T)
 while A.rows:
  ck(A[0,0]>=0)
  if A[0,0]==0:
   ck(all(A[0,j]==0 for j in range(A.cols)));A=A[1:,1:]
  else:
   A=A[1:,1:]-A[1:,0]*A[0,1:]/A[0,0]

# Rational unit normals on projective circle. Positive curvature weights define actual symmetric polygons.
sets=[[s.Rational(0),s.Rational(1)], [s.Rational(0),s.Rational(1,2),s.Rational(1)], [s.Rational(0),s.Rational(1,3),s.Rational(1),s.Rational(3)], [s.Rational(0),s.Rational(1,4),s.Rational(1,2),s.Rational(1),s.Rational(2)]]
cases=0
for ts in sets:
 for mode in range(4):
  us=[s.Matrix([(1-t*t)/(1+t*t),2*t/(1+t*t)]) for t in ts]
  N=len(us);A=s.Matrix(N,N,lambda i,j:abs(s.det(s.Matrix.hstack(us[i],us[j])))/4)
  masses=s.Matrix([s.Rational((i+1)**mode,1+mode) for i in range(N)])
  h=A*masses;V=(h.dot(masses))/2;nu=s.Matrix([h[i]*masses[i]/(2*V) for i in range(N)]);Nu=s.diag(*nu)
  T=s.diag(*[1/x for x in h])*A*s.diag(*masses)
  ck(T*s.ones(N,1)==s.ones(N,1));ck(Nu*T==(Nu*T).T);ck(sum(nu)==1)
  C=A.inv();D=-2*Nu*T.inv()-2*Nu+4*nu*nu.T
  H=-(s.diag(*h)*C*s.diag(*h)+s.diag(*[h[i]*masses[i] for i in range(N)]))/V+(s.diag(*h)*masses)*(s.diag(*h)*masses).T/V**2
  ck(D==H);ck(D*s.ones(N,1)==s.zeros(N,1))
  EE=2*Nu*(s.eye(N)+T)-4*nu*nu.T
  psd(D);psd(EE);psd(D-EE)
  B=s.Matrix(N,N-1,lambda i,j:(1 if i==j else (-nu[j]/nu[N-1] if i==N-1 else 0)))
  Z=-B.T*Nu*T*B
  psd(Z);ck(Z.det()>0)
  for slopes in itertools.product([-1,0,1],repeat=N):
   b=s.Matrix(slopes);q=b-s.ones(N,1)*(nu.dot(b));energy=sum(Nu[i,i]*T[i,j]*(q[i]+q[j])**2 for i in range(N) for j in range(N))
   ck(energy==(b.T*EE*b)[0]);ck((b.T*D*b)[0]>=energy)
  cases+=1

# Exact triangle identity and squared bound.
a,b,c=s.symbols('a b c',real=True)
ck(s.expand(2*a-((a+b)+(a+c)-(b+c)))==0)
psd(s.hessian(s.expand(3*((a+b)**2+(a+c)**2+(b+c)**2)-4*a*a),(a,b,c))/2)
# Source-sign completion coefficients and planar cubic obstruction.
t=s.symbols('t');delta=s.symbols('delta',positive=True)
Q=lambda a,b,c:4*a*b-(a+b-c)**2
ck(s.expand(Q(s.exp(t),s.exp(-t),2-delta)-(4-(2*s.cosh(t)-2+delta)**2)).rewrite(s.exp).simplify()==0)
Dhex=s.log((4-t*t)/(4-(t+2*s.cosh(t)-2)**2))
ck(s.series(Dhex,t,0,5).removeO().coeff(t,3)==s.Rational(1,2))
ck(s.limit((s.exp(-2*t)-s.exp(2*t))/t,t,0)==-4)
# Rate balance: s=delta^(1/5), variance<=delta/s^4, endpoint cap distance<=sqrt(s).
ck(s.Rational(1)-4*s.Rational(1,5)==s.Rational(1,5));ck(s.Rational(1,5)/2==s.Rational(1,10))
print(json.dumps({'status':'PASS','exact_assertions':count,'polygon_cases':cases,'arithmetic':'rational and symbolic; no floating proof claims','limits':'does not certify analytic estimates or novelty'},indent=2))
