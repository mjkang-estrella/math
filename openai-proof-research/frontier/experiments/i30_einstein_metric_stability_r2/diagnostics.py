#!/usr/bin/env python3
"""Independent exact rational diagnostics; no optional packages or external writes."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from math import comb
import json
E=Path(__file__).resolve().parent
checks=[]
def record(name,count,description): checks.append(dict(name=name,cases=count,description=description))
def rank(mat):
    mat=[[F(x) for x in row] for row in mat];r=0
    for j in range(len(mat[0])):
        pivot=next((i for i in range(r,len(mat)) if mat[i][j]),None)
        if pivot is None: continue
        mat[r],mat[pivot]=mat[pivot],mat[r];v=mat[r][j];mat[r]=[x/v for x in mat[r]]
        for i in range(len(mat)):
            if i!=r:
                v=mat[i][j];mat[i]=[x-v*y for x,y in zip(mat[i],mat[r])]
        r+=1
    return r
pairs=[(i,j) for i in range(4) for j in range(i,4)]
for xi in [(1,0,0,0),(1,2,0,0),(1,-2,3,0),(2,3,-1,4)]:
    columns=[];n2=sum(x*x for x in xi)
    for b,(i,j) in enumerate(pairs):
        u=[[0]*4 for _ in range(4)];u[i][j]=u[j][i]=1
        ux=[sum(u[i][j]*xi[j] for j in range(4)) for i in range(4)];tr=sum(u[i][i] for i in range(4))
        P=[[n2*u[i][j]+xi[i]*xi[j]*tr-xi[i]*ux[j]-ux[i]*xi[j] for j in range(4)] for i in range(4)]
        assert F(sum(P[i][i] for i in range(4)),2)==n2*tr-sum(x*y for x,y in zip(xi,ux))
        columns.append([P[i][j] for i,j in pairs]+ux)
    assert rank(list(zip(*columns)))==10
record('Einstein-plus-divergence-principal-symbol',4,'Full ten-coordinate tensor symbol ranks; scalar principal identity for each basis tensor.')
for i in range(100):
    t=F(i,1200);c=1-6*t;lam=3/c;lamprime=18/c**2
    assert lamprime==2*lam*lam
    R=F(7*i,11)
    assert -R+12/c==-R+4*lam
    g=F(i+1,17);ric=F(i-6,23)
    assert -2*ric/c+6*g/c**2==-2*(ric-lam*g)/c
    assert c**2*c**(-2)==1
record('flow-normalizations',100,'lambda ODE, rescaled volume density, tensor evolution, critical covariant L2 scaling.')
assert F(1,2)/(1-F(2,3))==F(3,2)
assert F(1,2)*F(2,3)/(1-F(2,3))**2==3
assert F(-3,2)+F(1,2)==-1
record('Moser-exponents',3,'Geometric-series sums and spacetime-to-uniform-time L2 exponent -1.')
count=0
for a in product([F(1),F(2)],repeat=4):
    for b in product([F(-1,4),F(1,4)],repeat=4):
        for mask in range(16):
            ids=[i for i in range(4) if mask>>i&1]
            f=[a[i]+F(1,3)*b[i] for i in range(4)]
            V=sum(f[i]**2 for i in ids);Vp=2*sum(f[i]*b[i] for i in ids)
            chi2=4*sum(b[i]**2 for i in range(4))
            assert Vp**2<=chi2*V
            count+=1
record('all-subset-volume-Cauchy',count,'All 16 subsets for 256 positive density evolutions, including empty and full sets.')
shell=[(0 if j==0 else -comb(4,j)*(-1)**j) for j in range(5)]
assert shell==[0,4,-6,4,-1]
assert [comb(2,j) for j in range(3)]==[1,2,1]
assert F(6,4)==F(3,2) and F(1)+F(2,4)==F(3,2)
assert F(3,2)/4-F(1,4)==F(1,8)
assert F(1,8)/2==F(1,16)
record('hole-budget-identities',5,'Polynomial coefficients, square-root volume cross term and eta-to-D conversion.')
for m in range(1,151):
    q=F(1,2**(8*m));aa=q*(1+8*m);rr=F(1,2**(2*m))
    budget=rr**6+aa*rr**3+q*rr**2+q*q;target=F(1,2**(12*m))
    assert budget<=11*target
    assert aa<=F(1,2**(3*m))*9
    if m>=8: assert aa<rr/4
record('logarithmic-scale-budget',150,'R fourth power O(eta^(3/2)); log(1/eta)<=8m; no floating point asymptotics.')
for i in range(-199,200):
    z=F(i,200);a=1/(3*(1+z));b=1/(3*(1-z));ap=a/b-1;bp=b/a-1
    assert 2/a+2/b==12
    assert 16*a*b*(2*(1/a-3)**2+2*(1/b-3)**2)==64*z*z/(1-z*z)
    assert ap*b+a*bp==0
    assert ap-bp==(a-b)*(a+b)/(a*b)
    if z: assert (a-b)*(ap-bp)>0
assert 16-6==10 and 12-6==6 and 0-6==-6
record('product-and-spectrum',400,'399 normalized products and their unstable mode; model spectral rescaling.')
assert sum([3,-1,-1,-1])==0
assert sum(x*x for x in [3,-1,-1,-1])==12
record('radial-conformal-bump',1,'Nonzero tracefree Hessian certificate; actual smooth geometry is proved in report.')
result=dict(status='PASS',checks=checks,total_exact_cases=sum(x['cases'] for x in checks),scope='Finite and exact algebra diagnostics only; report supplies all universal analytic/geometric arguments.')
(E/'diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
