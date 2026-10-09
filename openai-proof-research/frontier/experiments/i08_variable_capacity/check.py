"""Exact tests of the new local and flow identities; no asymptotic claims."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations
import json
import random

rng = random.Random(814229)


def multiply(p, q):
    out = defaultdict(int)
    for a, c in p.items():
        for b, d in q.items():
            out[tuple(x+y for x,y in zip(a,b))] += c*d
    return {a:c for a,c in out.items() if c}


def variable(i):
    return {tuple(int(j == i) for j in range(6)): 1}


def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for a,c in p.items():
            out[a] += c
    return dict(out)


x = [variable(i) for i in range(3)]
y = [variable(i+3) for i in range(3)]
ns = [add(x[i],y[i],multiply(x[(i+1)%3],y[(i+2)%3]),
          multiply(x[(i+2)%3],y[(i+1)%3])) for i in range(3)]
one = {(0,)*6:1}
linear = add(one, *[{a:-2*c for a,c in multiply(x[i],y[i]).items()} for i in range(3)])
poly = multiply(multiply(multiply(ns[0],ns[1]),ns[2]),linear)
pure = {a:c for a,c in poly.items() if not sum(a[:3]) or not sum(a[3:])}
assert pure == {(1,1,1,0,0,0):1,(0,0,0,1,1,1):1}
mixed_sum = sum(abs(c) for a,c in poly.items() if sum(a[:3])>=2 and sum(a[3:])>=2)
assert mixed_sum <= 448


def coords(p):
    return (p[0]+p[1]-p[2]-p[3],p[0]-p[1]+p[2]-p[3],p[0]-p[1]-p[2]+p[3])


def norm2(x):
    return sum(a*a for a in x)


def prod(x):
    result=F(1)
    for a in x: result*=a
    return result


points = [(F(1),F(0),F(0),F(0)),(F(1,4),)*4]
for _ in range(98):
    p = [rng.randrange(11) for _ in range(4)]
    if not sum(p): p[0]=1
    points.append(tuple(F(a,sum(p)) for a in p))
zero_normalizers=0
for p,q in zip(points, reversed(points)):
    x=coords(p); a=norm2(x); ha=abs(prod(x))
    b=norm2(coords(q)); hb=abs(prod(coords(q)))
    mout=F(0); tauout=F(0)
    for perm in permutations(range(4)):
        y=coords([q[i] for i in perm]); s=sum(u*v for u,v in zip(x,y)); z=1+s
        n=tuple(x[i]+y[i]+x[(i+1)%3]*y[(i+2)%3]+x[(i+2)%3]*y[(i+1)%3] for i in range(3))
        assert 0<=z<=4 and all(abs(v)<=z for v in n)
        if z:
            mout+=norm2(n)/z/24
            tauout+=prod(n)/(z*z)/24
            remainder=abs(prod(n)*s*s*(3+2*s)/(z*z))
            assert remainder<=36*s*s
        else:
            zero_normalizers+=1
            assert n==(0,0,0)
    assert mout>=a+b-7*(ha*b+a*hb)
    assert abs(tauout)<=ha+hb+460*a*b

kernel_cases=200
for _ in range(kernel_cases):
    n=rng.randrange(2,20)
    roots=[F(rng.randrange(1,11),10) for _ in range(n)]
    t=[q*q for q in roots]
    alpha=[1-q for q in t]
    z=[F(rng.randrange(1,20),7) for _ in range(n)]
    k={(i,j):prod(roots[i:j]) for i in range(n) for j in range(i+1,n+1)}
    for i in range(n):
        assert sum(alpha[j]*k[i,j] for j in range(i+1,n))<=2
    for j in range(1,n+1):
        assert sum(alpha[i]*k[i,j] for i in range(j))<=2
    double=sum(alpha[i]*alpha[j]*z[i]**3*z[j]*k[i,j]
               for i in range(n) for j in range(i+1,n))
    assert double<=2*sum(alpha[i]*z[i]**4 for i in range(n))

energy_cases=100
for _ in range(energy_cases):
    level=[(F(1),F(1))]  # probability and profile
    energy=F(0); noise=F(0)
    for depth in range(6):
        nxt=[]
        for probability, profile in level:
            split=F(rng.randrange(1,10),10)
            ts=[F(1)] if rng.randrange(4)==0 else [split,1-split]
            beta=1-sum(t*t for t in ts)
            energy+=probability*profile*profile*beta
            for t in ts:
                lam=F(rng.randrange(1,11),10); r=lam*lam
                child=profile*t/r
                noise+=probability*t*(1-r*r)*child*child
                nxt.append((probability*t,child))
        level=nxt
    terminal=sum(probability*profile*profile for probability,profile in level)
    assert energy<=1+noise-terminal

print(json.dumps({'polynomial_terms':len(poly),'mixed_absolute_coefficient_sum':mixed_sum,
 'posterior_orbit_pairs':len(points),'relative_permutations_each':24,
 'zero_normalizers':zero_normalizers,'kernel_cases':kernel_cases,
 'branching_energy_cases':energy_cases,'all_exact_checks_pass':True,
 'scope':'Finite identities and inequalities, not asymptotic proof or novelty.'},indent=2))
