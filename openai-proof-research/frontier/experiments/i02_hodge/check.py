"""Exact character bookkeeping, not a universal cycle-algebraicity test.
Run: python3 -I frontier/experiments/i02_hodge/check.py
"""
from fractions import Fraction
from math import gcd, prod
from itertools import product
from collections import Counter
import json

def character_data(n, a):
    ds = {j: int(-1 + sum(Fraction(j*x % n, n) for x in a)) for j in range(1,n)}
    ranks = {j: ds[j]+ds[n-j] for j in ds}
    return ds, ranks

def hodge_tensor(js, ds, ranks):
    p = Counter({0:1})
    for j in js:
        q = Counter()
        for k,v in p.items():
            q[k+1] += v*ds[j]
            q[k] += v*(ranks[j]-ds[j])
        p=+q
    return dict(sorted(p.items()))

out={}
for n,a in [(9,[1,1,1,6]),(84,[13,43,29,83]),(36,[5,19,13,35])]:
    ds,ranks=character_data(n,a)
    assert max(ranks.values()) == 2
    out[str(n)]={'genus':sum(ds.values()),'max_eigenspace_rank':max(ranks.values()),
        'primitive_h10':{j:ds[j] for j in ds if gcd(j,n)==1}}
ds,ranks=character_data(9,[1,1,1,6])
assert sum(ds.values())==7
assert sum(ds[j] for j in [1,4,7])==3
assert hodge_tensor([1,4,7],ds,ranks)=={1:4,2:4}
# N is the kernel of the explicit phase map, not an empirical cover search.
N=[a for a in product(range(9),repeat=3) if (a[0]+4*a[1]+7*a[2])%9==0]
assert len(N)==81
ann=[b for b in product(range(9),repeat=3) if all(sum(x*y for x,y in zip(a,b))%9==0 for a in N)]
assert set(ann)=={(j,4*j%9,7*j%9) for j in range(9)}
assert not any(sum(x!=0 for x in b)==1 for b in ann)
# C3 permutes factors; multiplication by 4 describes its action on the labels.
orbits=[]; seen=set()
for j in range(1,9):
    if j in seen:continue
    orb=sorted({j,4*j%9,7*j%9});seen.update(orb);orbits.append(orb)
primitive=Counter(); all_inv=Counter()
for orb in orbits:
    j=orb[0];ht=hodge_tensor([j,4*j%9,7*j%9],ds,ranks)
    # Orbits of length 3: invariant diagonal equals one tensor summand.
    # Orbits of length 1: j=3 or 6, each tensor factor is a 1D space;
    # a 3-cycle has positive Koszul sign.
    assert len(orb)==3 or prod(ranks[k] for k in [j,4*j%9,7*j%9])==1
    all_inv.update(ht)
    if gcd(j,9)==1: primitive.update(ht)
assert dict(primitive)=={1:8,2:8}
assert dict(sorted(all_inv.items()))=={0:1,1:8,2:8,3:1}
out['quotient9']={'kernel_size':len(N),'annihilator':ann,'C3_orbits':orbits,
    'primitive_H3_by_p':dict(sorted(primitive.items())),
    'singular_quotient_H3_by_p':dict(sorted(all_inv.items())),
    'H1_invariant_dimension':0,
    'warning':'Resolution may add cohomology. No coniveau or algebraicity conclusion.'}
print(json.dumps(out,indent=2))
