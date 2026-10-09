"""Search 4-point cyclic covers y^N = prod (x-x_k)^{a_k} with a cubic real subfield structure
giving eigen-signatures (1,1),(2,0),(0,2) on the three conjugate pairs, i.e. Mumford-partner families.
d_j = -1 + sum_k <j a_k / N>  (dim H^{1,0} of the zeta^j eigenspace, standard convention up to j->-j)."""
from fractions import Fraction as Fr
from math import gcd
import itertools
def frac(x): return x - (x.numerator//x.denominator)
for N in [7,9,14,18]:
    units=[j for j in range(1,N) if gcd(j,N)==1]
    seen=set()
    for a in itertools.product(range(1,N),repeat=4):
        if sum(a)%N: continue
        if gcd(gcd(gcd(a[0],a[1]),gcd(a[2],a[3])),N)!=1: continue
        key=tuple(sorted(a))
        if key in seen: continue
        seen.add(key)
        d={j: -1+sum(Fr(j*ak% N,N) for ak in a) for j in range(1,N)}
        # primitive characters only (others come from quotient curves)
        pairs=[(j,N-j) for j in units if j< N-j]
        sig=[(d[j],d[N-j]) for (j,_) in pairs]
        if sorted(sig)==sorted([(1,1),(2,0),(0,2)]) or sorted(sig)==sorted([(1,1),(2,0),(2,0)]) or sorted(sig) in (sorted([(1,1),(0,2),(0,2)]),):
            nonprim={j:(d[j],d[N-j]) for j in range(1,N) if gcd(j,N)!=1 and j<N-j}
            print(N,key,"prim pairs",dict(zip([p[0] for p in pairs],sig)),"nonprim",nonprim)
