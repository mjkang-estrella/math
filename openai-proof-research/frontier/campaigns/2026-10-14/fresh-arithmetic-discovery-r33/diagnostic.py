#!/usr/bin/env python3
"""MIT; exact finite arithmetic, not a surface-realization proof."""
from functools import lru_cache
from math import gcd
import json
@lru_cache(None)
def comps(n):
    if n==0:return ((),)
    return tuple((k,)+t for k in range(1,n+1) for t in comps(n-k))
def K(a):
    x,y=1,0
    for k in a:x,y=k*x+y,x
    return x+y
B=12
blocks={c:[] for c in range(2,B+1)}
for c in blocks:
    for n in range(1,c):
        for a in comps(n):blocks[c].append((K(a),K(a[1:])+c-n-1,(a,c-n)))
states=[{} for _ in range(B+1)];states[0][(1,0)]=()
F=[0,1]
for _ in range(B+1):F.append(F[-1]+F[-2])
out=[]
for b in range(2,B+1):
    for c in range(2,b+1):
        for (k,s),w in states[b-c].items():
            for kb,qb,desc in blocks[c]:states[b].setdefault((k*kb,s*kb+qb),w+(desc,))
    assert all(k<=F[b+1] for k,s in states[b])
    assert max(k for k,s in states[b])==F[b+1]
    best=max(states[b],key=lambda z:(z[0]-1)//gcd(z[0]-1,z[1]))
    k,s=best
    out.append(dict(b=b,states=len(states[b]),max_formula_index=(k-1)//gcd(k-1,s),bound=F[b+1]-1,witness=states[b][best]))
assert out[7]['max_formula_index']==49 and out[8]['max_formula_index']==80
print(json.dumps({'status':'PASS','scope':'all ordered positive component data of costs 2 through 12','rows':out},indent=2))
