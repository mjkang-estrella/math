#!/usr/bin/env python3
"""Bounded exact diagnostics only; no numerical output is a proof."""
import os, resource
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:
    os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
import json
from pathlib import Path
import sympy as s
x,a,b=s.symbols('x a b',real=True)
# p=2, alpha=1: check generalized-axisymmetric PDE exactly.
K=1/((a-x)**2+b*b)
pde=s.factor(s.diff(K,a,2)+s.diff(K,b,2)+2*s.diff(K,b)/b)
assert pde==0
# Rational evaluation matrices: sample nonsingularity, not the all-node theorem.
cases=[[(0,1)],[(0,1),(2,1)],[(0,1),(0,2)],[(0,0),(2,1)],
       [(-2,1),(0,2),(3,1)], [(-2,0),(0,1),(3,0)]]
results=[]
for profiles in cases:
    n=len(profiles);nodes=list(range(7,7+2*n));cols=[]
    for center,height in profiles:
        R=(x-center)**2+height**2
        cols.extend([1/R**2,(x-center)/R**2])
    M=s.Matrix([[f.subs(x,t) for f in cols] for t in nodes])
    det=M.det();assert det!=0
    results.append({'profiles':profiles,'nodes':nodes,'determinant':str(det)})
# Clear denominators only away from actual poles. Three signed rational cases.
sturm=[]
for profiles,charges in [(cases[1],[1,1]),(cases[2],[1,-2]),(cases[4],[1,-3,2]),(cases[5],[1,-1,2])]:
    F=sum(s.Rational(c)/((x-a0)**2+b0*b0) for (a0,b0),c in zip(profiles,charges))
    num,den=s.fraction(s.cancel(s.diff(F,x)))
    P=s.Poly(num,x);g=s.gcd(P,s.Poly(den,x));assert g.degree()==0
    roots=P.count_roots(-s.oo,s.oo)
    assert roots<=2*len(profiles)-1
    sturm.append({'profiles':profiles,'charges':charges,'numerator':str(num),'real_distinct_roots':int(roots)})
# Canceled profile domain bookkeeping: original puncture 0 remains excluded.
F=1/x**2-1/x**2+1/((x-2)**2+1)
assert s.cancel(F-1/((x-2)**2+1))==0
assert s.diff(F,x).subs(x,2)==0
# Castle critical equation correspondence without transcendental asymptotics.
z,p,t=s.symbols('z p t')
phi=z+1
assert s.expand((1-phi)*(p+phi)+t*phi)==-s.expand(z*z+(1+p-t)*z-t)
r=(s.sqrt(5)-1)/2
assert s.simplify(1-r-r*r)==0
assert s.simplify(12*((1+s.sqrt(5))/2-1)/((1+s.sqrt(5))/2+1)-s.sqrt(5))>0
out={'pde_zero':True,'evaluation_matrices':results,'sturm_cases':sturm,
     'cancellation_and_critical_mapping':True,'limit':'512MiB address space, 35 CPU seconds, BLAS1; finite diagnostics only'}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2))
print('PASS: exact PDE; 6 finite evaluation matrices; 4 Sturm counts; cancellation; Castle saddle map')
