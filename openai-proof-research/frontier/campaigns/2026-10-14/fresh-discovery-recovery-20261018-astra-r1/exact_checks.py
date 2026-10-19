#!/usr/bin/env python3
"""Exact finite jets only; analytic existence and positivity are proved in report.md."""
from fractions import Fraction as Q
from math import comb, factorial
import json
N=16

def data(a0,a1,c=Q(1),B=Q(2)):
    a=[Q(0)]*(N+1);a[0]=Q(a0);a[1]=Q(a1)
    for n in range(N-1):
        a[n+2]=((B*n-1)*a[n]+(c*a[n-2] if n>=2 else 0))/((n+2)*(n+1))
    return a

def lift(a):
    p={}
    for k in range(N//2+1):
        for n in range(N-2*k+1):
            val=sum(Q(comb(k,j)*factorial(n+2*j),factorial(n))*a[n+2*j] for j in range(k+1))
            if val:p[n,2*k]=(-1)**k*val/factorial(2*k)
    return p

def deriv(p,idx):
    r={}
    for a,b in p:
        z=(a,b)[idx]
        if z:r[(a-1,b) if idx==0 else (a,b-1)]=z*p[a,b]
    return r

def add(*ps):
    r={}
    for p in ps:
        for k,v in p.items():r[k]=r.get(k,Q(0))+v
    return {k:v for k,v in r.items() if v}

def scale(p,c):return {k:c*v for k,v in p.items() if c*v}
def mul(p,q):
    r={}
    for (a,b),v in p.items():
        for (c,d),w in q.items():
            if a+b+c+d<=N:r[a+c,b+d]=r.get((a+c,b+d),Q(0))+v*w
    return {k:v for k,v in r.items() if v}
def det(a,b):return add(mul(a[0],b[1]),scale(mul(a[1],b[0]),-1))
def jet(p,n):return {k:v for k,v in p.items() if sum(k)<=n}
def fmt(p):return {f'{a},{b}':str(v) for (a,b),v in sorted(p.items())}

u,v=lift(data(1,0)),lift(data(0,1))
checks={}
for name,p in [('u',u),('v',v)]:
    residual=add(deriv(deriv(p,0),0),deriv(deriv(p,1),1),p)
    checks[name+'_helmholtz_through_degree14']=not jet(residual,N-2)
    checks[name+'_neumann']=all(b%2==0 for a,b in p)
checks['u_even_s']=all(a%2==0 for a,b in u)
checks['v_odd_s']=all(a%2==1 for a,b in v)
Fs=(deriv(u,0),deriv(v,0));Ft=(deriv(u,1),deriv(v,1));J=det(Fs,Ft)
checks['jacobian_leading_cubic']=jet(J,3)=={(2,1):Q(1),(0,3):Q(1,3)}
checks['normal_u_quartic']=u.get((0,4))==Q(-1,12) and u.get((0,2),0)==0
checks['normal_v_zero']=all(a>0 for a,b in v)
checks['all_J_terms_odd_t_even_s']=all(b%2==1 and a%2==0 for a,b in J)
F0=tuple({(a,0):w for (a,b),w in p.items() if b==0} for p in [u,v])
F0s=tuple(deriv(p,0) for p in F0)
D=det(F0,F0s)
checks['wronskian_exp_s_squared']=jet(D,14)=={(2*k,0):Q(1,factorial(k)) for k in range(8)}
a=add(D,scale(det(F0s,tuple(deriv(p,0) for p in F0s)),-1))
checks['boundary_coefficient_s_squared_exp_s_squared']=jet(a,12)=={(2*k+2,0):Q(1,factorial(k)) for k in range(6)}
checks['jacobian_boundary_normal_derivative_matches']=jet({(i,0):w for (i,j),w in J.items() if j==1},12)==jet(a,12)
# A second parameter pair and negative controls check the general cubic coefficient.
parameter=[]
for c,B in [(Q(2),Q(5)),(Q(1),Q(1)),(Q(2),Q(1)),(Q(0),Q(2))]:
    U,V=lift(data(1,0,c,B)),lift(data(0,1,c,B))
    jj=det((deriv(U,0),deriv(V,0)),(deriv(U,1),deriv(V,1)))
    expect={(2,1):c,(0,3):(B-c)/3};expect={k:x for k,x in expect.items() if x}
    ok=jet(jj,3)==expect
    checks[f'general_parameters_{c}_{B}']=ok
    parameter.append({'c':str(c),'B':str(B),'J_degree3':fmt(jet(jj,3))})
checks['wrong_quartic_coefficient_rejected']=u.get((0,4))!=Q(-1,24)
checks['wrong_linear_J_bound_rejected']=J.get((0,1),Q(0))==0
checks['normal_quadratic_displacement_absent']=u.get((0,2),Q(0))==0
assert all(checks.values()),checks
print(json.dumps({'purpose':'supporting exact finite jets, not proof of global target','checks':checks,'passed':len(checks),'J_degree7':fmt(jet(J,7)),'u_normal_through8':fmt({k:w for k,w in u.items() if k[0]==0 and k[1]<=8}),'parameters':parameter},indent=2,sort_keys=True))
