#!/usr/bin/env python3
"""Bounded exact normalization checks. No numerical evidence is a proof gate.
Run with python -B; writes nothing. Uses only the standard library.
"""
from fractions import Fraction as F
import json

checks = []
def check(label, condition):
    if not condition:
        raise AssertionError(label)
    checks.append(label)

def add(a,b):
    d=dict(a)
    for k,v in b.items(): d[k]=d.get(k,F(0))+v
    return {k:v for k,v in d.items() if v}
def mul(a,b):
    d={}
    for k,v in a.items():
        for l,w in b.items(): d[k+l]=d.get(k+l,F(0))+v*w
    return {k:v for k,v in d.items() if v}
def solve_radial(n,p):
    # -Delta inverse of sum p[k] r^(n+2k), zero trace at r=1.
    d={}
    for k,v in p.items():
        c=v/F(4*(k+1)*(n+k+1))
        d[0]=d.get(0,F(0))+c
        d[k+1]=d.get(k+1,F(0))-c
    return {k:v for k,v in d.items() if v}
def moment_poly(n,p):
    return sum((v/F(2*(n+k+1)) for k,v in p.items()),F(0))

def riccati_series(n,degree):
    # Descending finite continued fraction; depth degree suffices to this order.
    h=[F(0)]*(degree+1)
    for level in reversed(range(n,n+degree+1)):
        d=F(2*(level+1)); new=[F(0)]*(degree+1)
        # h_new=(a/d)*sum (h_old/d)^j, truncated.
        term=[F(0)]*(degree+1);term[0]=F(1)
        for j in range(degree):
            for k in range(degree):new[k+1]+=term[k]/d
            prod=[F(0)]*(degree+1)
            for k in range(degree+1):
                for l in range(degree+1-k):prod[k+l]+=term[k]*h[l]/d
            term=prod
        h=new
    return h

for n in range(9):
    p={0:F(1)}; coeff=[]
    for j in range(1,5):
        coeff.append(moment_poly(n,p));p=solve_radial(n,p)
    check('constant_resolvent_vs_riccati_n%d'%n,coeff==riccati_series(n,4)[1:])

for n in range(2,35):
    def an(k,b):return F(1,2*(k+2))-b/F(2*(k+1))
    weights=[1,-4,6,-4,1]
    beta=F(12,(n-1)*n*(n+1)*(n+2)*(n+3))
    for b in [F(0),F(1,12),F(1,6),F(1,4)]:
        difference=sum((weights[j]*an(n-2+j,b) for j in range(5)),F(0))
        expected=beta*(F(n-1,n+4)-b)
        check('weighted_difference_n%d_b%s'%(n,b),difference==expected)
    check('beta_lower_bound_n%d'%n,beta>=F(1,(n+1)**5))

# Exact complex arithmetic for the nullspace first-variation contraction.
def zadd(a,b):return(a[0]+b[0],a[1]+b[1])
def zmul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def zconj(a):return(a[0],-a[1])
def zabs2(a):return a[0]**2+a[1]**2
def zdiv(a,b):return tuple(v/zabs2(b) for v in zmul(a,zconj(b)))
def zscale(a,c):return(a[0]*c,a[1]*c)
pts=[(F(1),F(0)),(F(0),F(1)),(F(-1),F(0)),(F(0),F(-1))]
coef=[1,-1,1,-1]
for z in [(F(0),F(0)),(F(1,3),F(1,5)),(F(-2,5),F(1,7))]:
    r2=zabs2(z); B=[]
    # pi P_s=(1-r^2)/(2|s-z|^2), so every B here is pi times B in the notes.
    for k in range(3):
        val=(F(0),F(0))
        for s,c in zip(pts,coef):
            power=(F(1),F(0))
            for j in range(k):power=zmul(power,s)
            ps=(1-r2)/(2*zabs2(zadd(s,zscale(z,-1))))
            val=zadd(val,zscale(power,c*ps))
        B.append(val)
    lhs=6*B[0][0]**2-8*zabs2(B[1])+2*zabs2(B[2])
    z2=zmul(z,z);z4=zmul(z2,z2)
    H=zdiv((F(4),F(0)),zadd((F(1),F(0)),zscale(z4,-1)))
    rhs=(1-r2)**4*zabs2(H)/2
    check('first_variation_contraction_'+str(z),lhs==rhs)

print(json.dumps({'status':'PASS_BOUNDED_EXACT_CHECKS','count':len(checks),
 'checks':checks,'limits':'No test of the infinite-mode estimate, weak-derivative argument, contribution, or full theorem. These are exact supporting identities only.'},indent=2))
