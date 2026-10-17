#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Finite adversarial checks of new interfaces, not a universal proof."""
from itertools import product
from math import isqrt
import json

def tournament(p,h):
    rows=list(product(range(p),repeat=h)); H={a*a%p for a in range(1,p)}
    edges={}
    for u in rows:
        for v in rows:
            if u==v:continue
            z=next((b-a)%p for a,b in zip(u,v) if a!=b)
            if z in H:edges[u,v]=z
    return rows,H,edges

def good(S,E):
    values={}
    for (u,v),c in E.items():
        if u in S and v in S:
            if v in values and values[v]!=c:return False
            values[v]=c
    return True

def exhaustive(p,h):
    rows,H,E=tournament(p,h)
    assert all(((u,v) in E)!=((v,u) in E) for u in rows for v in rows if u!=v)
    assert all(sum((u,v) in E for v in rows)==(p**h-1)//2 for u in rows)
    largest=0
    for mask in range(1<<len(rows)):
        S={v for j,v in enumerate(rows) if (mask>>j)&1}
        if good(S,E):largest=max(largest,len(S))
    assert largest<=3**h
    return dict(p=p,h=h,subsets=1<<len(rows),max_head_constant=largest)

out={'exhaustive':[exhaustive(3,1),exhaustive(7,1),exhaustive(3,2)]}
# The putative stronger bound 3^h-1 fails; h=4,p=3 has all labels1.
rows,H,E=tournament(3,4)
assert len(rows)==81 and H=={1} and good(set(rows),E)
out['negative_strict_81_bound']='rejected by all81 rows at p=3,h=4'
# Full covariance and one orbit on row-position pairs for a nontrivial H.
rows,H,E=tournament(7,2)
for a in H:
    for b in rows:
        T=lambda v:tuple((a*z+w)%7 for z,w in zip(v,b))
        for (u,v),c in E.items():assert E[T(u),T(v)]==a*c%7
orbit={(b,c) for b in rows for c in H}
assert len(orbit)==len(rows)*len(H)==147
out['covariance']={'p':7,'h':2,'affine_maps':len(H)*len(rows),'oriented_edges_per_map':len(E),'orbit_size':len(orbit)}
# Row translations alone leave the label coordinate fixed, hence fail full transitivity.
assert len(rows)<len(orbit)
out['negative_row_only_transitivity']='rejected: orbit49<147'
# Miniature nested predicate: depth1,h1,p3,M1,L3, outside asymptotic parameter window.
# Exhaust all512 raw inputs and coordinate-group generators. No ratio claim here.
def mini(x):
    chunks=[(x>>(3*j))&7 for j in range(3)]
    weak=[a.bit_count()>=2 for a in chunks]
    strong=[a==7 for a in chunks]
    return any(strong[j] and not weak[(j+1)%3] for j in range(3))
def permute(x,pi):return sum(((x>>i)&1)<<pi[i] for i in range(9))
gens=[[(i+3)%9 for i in range(9)]]
for b in range(3):
    for off in (0,1):
        pi=list(range(9));i=3*b+off;pi[i],pi[i+1]=pi[i+1],pi[i];gens.append(pi)
S=[0,0]
for x in range(512):
    y=mini(x);S[y]=max(S[y],sum(mini(x^(1<<i))!=y for i in range(9)))
    for pi in gens:assert mini(permute(x,pi))==y
assert not mini(0)
blocks=[7<<(3*j) for j in range(3)]
assert all(mini(b) for b in blocks) and all(a&b==0 for i,a in enumerate(blocks) for b in blocks[i+1:])
out['miniature']={'raw_inputs':512,'generators':len(gens),'sides':S,'zero_blocks':len(blocks)}
# Integer-only constant checks; no floating-point positivity accepted.
assert 3**20>2**20*1936
out['seed_margin']={'numerator':3**20,'denominator':2**20*1936}
for p in (167,179,191,239):
    A=(p**4-1)//2;M=isqrt(A)+(isqrt(A)**2<A);r=(p-1)//2
    assert 2*M>=p*p and 5*M<=4*p*p
    assert p*max(r,82)<=M
    assert 2*p**4>=3*M*M
out['integer_parameters']='checked p=167,179,191,239; universal inequalities proved in candidate'
print(json.dumps(out,indent=2))
