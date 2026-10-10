#!/usr/bin/env python3
"""Exact interface diagnostics; neither a proof audit nor a novelty oracle."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from itertools import product
import json

checks = 0
def eq(x, y):
    global checks
    assert x == y, (x, y)
    checks += 1
def yes(x):
    global checks
    assert x
    checks += 1
def dot(x,y): return sum(a*b for a,b in zip(x,y))

# Full homogeneous gradient radial Jacobian, tested without square roots.
# p=sqrt(theta.Q.theta), X=theta/p. Tangent Gram determinant for n=3.
theta=(F(3,5),F(4,5),F(0)); tangents=[(F(-4,5),F(3,5),F(0)),(F(0),F(0),F(1))]
radial=[]
for Q in [(1,1,1),(1,4,9),(9,2,5)]:
    qt=tuple(q*t for q,t in zip(Q,theta)); p2=dot(theta,qt)
    # DX(v)=p^-1 [v-theta*(Qtheta.v)/p²].
    B=[tuple(v[i]-theta[i]*dot(qt,v)/p2 for i in range(3)) for v in tangents]
    gram=[[dot(v,w)/p2 for w in B] for v in B]
    jac2=gram[0][0]*gram[1][1]-gram[0][1]**2
    full_grad2=dot(qt,qt)/p2
    eq(jac2,full_grad2/p2**3)
    tangent_grad2=full_grad2-p2
    if Q==(1,1,1): eq(tangent_grad2,0); eq(jac2,1)
    radial.append(str(jac2))

# Signed weak residual is not total variation without uniform BV control.
# Alternating +/-1 on 2N equal intervals; primitive consists of N triangles.
oscillations=[]
for N in [1,2,3,7,16,100]:
    h=F(1,2*N); primitive=F(0); integral=F(0)
    for k in range(2*N):
        nxt=primitive+(-1 if k%2 else 1)*h
        integral+=(primitive+nxt)*h/2
        primitive=nxt
    eq(primitive,0);eq(integral,F(1,4*N))
    eq(sum(h for _ in range(2*N)),1)
    # |int g f| <= Lip(g)*int |primitive|; TV(f)=2(2N-1).
    oscillations.append(dict(N=N,weak_bound=str(integral),L1=1,BV=2*(2*N-1)))

# Convex gradient transverse averages on the full cube, not a measure-zero axis.
# Phi=|z|²/2+eta*z1²*z2², 0<=eta<=1/8; Gershgorin gives Hessian>=1/2.
# Uniform cube expectation of a monomial.
def moment(k): return F(0) if k%2 else F(1,k+1)
for eta in [F(0),F(1,100),F(1,8)]:
    yes(1-4*eta>=F(1,2))
    per_coordinate=4*eta**2*moment(2)*(moment(4)-moment(2)**2)
    eq(2*per_coordinate,F(32,135)*eta**2)
    eq(8*2*per_coordinate,F(256,135)*eta**2)
    mixed_sum=2*16*eta**2*moment(2)**2
    eq(mixed_sum,F(32,9)*eta**2)
    # Actual averaged gradient components differ from axis restrictions.
    eq((1+2*eta*moment(2))-1,F(2,3)*eta)

# One compatible product: independent convex combinations expand to combinations
# of joint image values, with tensor-product weights.
xs=[(F(-2),F(1)),(F(2),F(-1))]; ys=[(F(-3),),(F(1),),(F(4),)]
wx=[F(1,3),F(2,3)]; wy=[F(1,4),F(1,2),F(1,4)]
weights=[a*b for a,b in product(wx,wy)]
eq(sum(weights),1)
mix=tuple(sum(w*(x+y)[j] for w,(x,y) in zip(weights,product(xs,ys))) for j in range(3))
separate=tuple(sum(w*x[j] for w,x in zip(wx,xs)) for j in range(2))+(sum(w*y[0] for w,y in zip(wy,ys)),)
eq(mix,separate)

# Product boundary Jacobian: block dimensions 1 and 2, arbitrary box side lengths.
for s1,s2 in [(F(2),F(3)),(F(1,4),F(5,2)),(F(1),F(1))]:
    lengths=(F(2),F(3),F(5)); scales=(s1,s2,s2); determinant=s1*s2**2
    for i in range(3):
        old=1;new=1
        for j in range(3):
            if j!=i:old*=lengths[j];new*=lengths[j]*scales[j]
        eq(new/old,determinant/scales[i])

# Both endpoint log-volume coefficients with trace m: log K#=log D+t m,
# log L#=log D-(1-t)m, m=log K-log L, log D=(1-t)log K+t log L.
for t in [F(1,7),F(1,3),F(1,2),F(6,7)]:
    eq((1-t+t,t-t),(F(1),F(0)))
    eq((1-t-(1-t),t+(1-t)),(F(0),F(1)))

# Rate arithmetic: a>=1, 0<b<=1. Exact inequalities and complete exponent chain.
for n,a,b in product(range(3,10),[F(1),F(7,2),F(1000)],[F(1),F(1,2),F(1,1000)]):
    theta=b/(8*(a+b+1)); core=F(1,2)-a/(8*(a+b+1))
    yes(core>=F(3,8));yes(2*theta<=F(1,4));yes(core>=2*theta)
    alpha=64*n*(n+2)*(a+b+1)/b
    eq(theta/F(4*(n+2))/F(2*n),1/alpha)

print(json.dumps(dict(status='PASS',exact_assertions=checks,
 scope='Finite exact interface diagnostics, not I50 proof approval or priority certification',
 radial_J_squared=radial,oscillation=oscillations,
 cube_error_expectation='32 eta^2 / 135',mixed_Hessian_expectation='32 eta^2 / 9',
 exponent='64 n(n+2)(a+b+1)/b'),indent=2))
