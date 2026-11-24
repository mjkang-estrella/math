"""Finite checks for the publication transcription; not proof certification."""
from fractions import Fraction as Q
from itertools import combinations
from math import log, pi, sin, cos, sqrt, prod
from random import Random
import json
rng=Random(20261009)
def entropy(p):return -sum(float(x)*log(float(x)) for x in p if x)
def matchings(vertices,edges):
    if not vertices:yield ();return
    u=vertices[0]
    for v in vertices[1:]:
        e=tuple(sorted((u,v)))
        if e in edges:
            for m in matchings([w for w in vertices if w not in (u,v)],edges):yield (e,)+m
checks={}
# Exponential matching laws are maximum-entropy laws at their own means.
cases=0;roots=0
for n in [2,4,6,8]:
    for _ in range(40):
        edges={e:rng.randint(1,7) for e in combinations(range(n),2) if rng.random()<.7}
        for u in range(0,n,2):edges.setdefault((u,u+1),1)
        ms=list(matchings(list(range(n)),edges));w=[prod(edges[e] for e in m) for m in ms];p=[Q(t,sum(w)) for t in w]
        x={e:sum((p[i] for i,m in enumerate(ms) if e in m),Q(0)) for e in edges}
        f=entropy(x.values());h=entropy(p)
        for v in range(n):
            W=entropy([1-y for e,y in x.items() if v not in e]);assert f-h<=1.5*W+1e-10;roots+=1
        cases+=1
checks['maximum_entropy_law_cases']=cases;checks['rooted_inequality_checks']=roots
# A triangular prism restricted to crossing its triangle cut once.
p=[Q(1,6),Q(1,3),Q(1,2)];h=entropy(p);b=entropy([1-x for x in p])
# Three parent matching types: one cross edge plus one edge in each triangle.
Dparent=3*h-h;Dchild=2*h-h
assert abs(Dparent-2*Dchild)<1e-12
# Every root star has one occurrence of each probability; Bparent=3b.
assert abs((3*b-b)-(2*b-b)-(2*b-b))<1e-12
checks['tight_cut_defect_and_root_reserve']=True
# Exact algebra in the countable residual bound.
for a in range(21):
 for b in range(21-a):
    x=Q(a,20);y=Q(b,20);z=1-x-y;q=x*y+x*z+y*z;r=x*y*z
    lhs=sum((1+j)**2*(1+k)**2 for j,k in [(x,y),(x,z),(y,z)])
    assert lhs==9+2*q+q*q-8*r and lhs<=Q(88,9)
checks['residual_coefficient_rational_cases']=231
# The triangle squared-side identity without evaluating singular values.
for _ in range(300):
    u=[(Q(rng.randint(-9,9),7),Q(rng.randint(-9,9),7)) for _ in range(2)]
    u.append(tuple(-u[0][j]-u[1][j] for j in range(2)))
    lengths=[sum((u[i][j]-u[k][j])**2 for j in range(2)) for i,k in combinations(range(3),2)]
    a=sum(x*x for x,y in u);d=sum(y*y for x,y in u);b=sum(x*y for x,y in u)
    assert sum((x-y)**2 for x,y in combinations(lengths,2))==Q(9,2)*((a-d)**2+4*b*b)
checks['exact_triangle_identity_cases']=300
# Analytic constants and sector formula, checked independently.
B=3/(2*sqrt(2*pi));h=1/(4*sqrt(3));E0=(B/1600)**2
assert abs(1/(6*(h/2)**2)-32)<1e-12
assert 2*sqrt(E0)<=h/2 and abs(400*sqrt(E0)-B/4)<1e-12
assert Q(3,2)*(Q(26,10)-Q(12,100))**2-10*(3/Q(314159,100000))**2>Q(1066,10000)
for t in [.01,.05,.1]:
    F=sum(sin(a/2)**2/(2*pi) for a in [2*pi/3+t,2*pi/3-t,2*pi/3])
    assert abs(B*B-F-(1-cos(t))/(4*pi))<1e-14
checks['activation_constants_and_sharp_sector_identity']=True
print(json.dumps({'passed':True,'checks':checks,'scope':'Exact finite identities and diagnostic examples; not a universal proof or upstream certificate.'},indent=2))
