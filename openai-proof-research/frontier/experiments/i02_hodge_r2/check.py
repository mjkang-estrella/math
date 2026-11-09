"""Independent exact checks; no imports from earlier research scripts.
Run with python3 -I. These checks do not prove cycle algebraicity.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd
import json

# Regular differentials x^m dx/y^k: orders 8-k at finite branch points
# and k-4-3m at each of the three points over infinity.
hol = [(k,m) for k in range(1,9) for m in range(4)
       if 8-k >= 0 and k-4-3*m >= 0]
assert hol == [(4,0),(5,0),(6,0),(7,0),(7,1),(8,0),(8,1)]
basis = [(k,m,1) for k,m in hol] + [(9-k,m,0) for k,m in hol]
N = [v for v in product(range(9), repeat=3)
     if (v[0]+4*v[1]+7*v[2]) % 9 == 0]
ann = [v for v in product(range(9), repeat=3)
       if all(sum(a*b for a,b in zip(v,n)) % 9 == 0 for n in N)]
assert len(N) == 81
assert set(ann) == {(j,4*j%9,7*j%9) for j in range(9)}
survivors = [v for v in product(basis,repeat=3)
             if tuple(b[0] for b in v) in ann]
assert len(survivors) == 50
seen = set(); orbits = []
for v in survivors:
    if v in seen: continue
    orb = {v, v[1:]+v[:1], v[2:]+v[:2]}
    seen.update(orb); orbits.append(orb)
Y = Counter(); U = Counter(); old = Counter()
for orb in orbits:
    v = next(iter(orb)); p = sum(x[2] for x in v)
    Y[p] += 1
    (U if v[0][0] % 3 else old)[p] += 1
assert Y == {0:1,1:8,2:8,3:1}
assert U == {1:8,2:8} and old == {0:1,3:1}
# The other H^3 Kunneth types are permutations of (2,1,0).
assert all(sum(x != 0 for x in v) != 1 for v in ann)
# A single-coordinate phase delta_1^a normalizes the permutation subgroup
# modulo N iff its conjugation difference (-a,a,0) belongs to N.
normalizing = [a for a in range(9) if (-a+4*a)%9 == 0]
assert normalizing == [0,3,6]
M = {v for v in product(range(9),repeat=3) if sum(v)%3 == 0}
assert len(M) == 243 and set(N) <= M
assert M == {((a+3*k)%9,b,c) for a,b,c in N for k in range(3)}

# Arapura 3.4(b), with D coefficients reduced modulo 9.
branch = [(1,1,1,6),(4,4,4,6),(7,7,7,6)]
Lminus8 = [-8*sum(a)//9 + sum((8*x)//9 for x in a) for a in branch]
assert Lminus8 == [-3,-2,-1]
h3 = 1
for a in Lminus8: h3 *= max(-a-1,0)
assert 6*h3 == 0 < len(survivors)

def curve(n,a):
    assert sum(a)%n == 0 and gcd(n,*a) == 1
    d = {j: int(-1+sum(Fraction((j*x)%n,n) for x in a))
         for j in range(1,n)}
    ranks = {j:d[j]+d[n-j] for j in d}
    genus = 1+(-2*n+sum(n-gcd(n,x) for x in a))//2
    assert sum(d.values()) == genus
    return {'genus':genus,'h10':d,'ranks':ranks}
t3 = curve(3,[1,7,7,7,7,-29])
t9 = curve(9,[-4,7,7,7,7,-24])
assert t3['genus'] == 4 and t9['genus'] == 15
assert all(t9['ranks'][j] == 4 for j in [1,2,4,5,7,8])

# Monomial identities for W: w=z^3/(f2*f3^2), z^9=f1*f2^4*f3^7.
assert [x-3*y for x,y in zip([1,4,7],[0,1,2])] == [1,1,1]
# First incidence family f1=s*b, f2=b, f3=P*b has b exponent 12.
assert 1+4+7 == 12
# v=z^3/b^4, so v^3=s*P^7. tau:z->zeta_3*z fixes v.
assert 3 % 3 == 0
# Second family f1=l, f2=l^2/s, f3=P has l exponent nine.
assert 1+2*4 == 9
# On its lift y2=y1^2/a, y3=b: z=y1^9*b^7/a^4.
z_exponents = [1+2*4, -4, 7]  # y1, a, b
assert z_exponents == [9,-4,7]
# Recover b from b^7=v*a^4 and b^9=P: b=(v*a^4)^4/P^3.
assert 7*4-9*3 == 1

# Kunneth-degree certificate: graph S->X3 has degrees (2,0),(1,1),(0,2).
# The divisor of y1^2-a*y2 has only pure degree-two classes on S,X1,X2.
Rdegrees = [(2,0,0,0),(0,2,0,0),(0,0,2,0)]
Gdegrees = [(2,0,0,0),(1,0,0,1),(0,0,0,2)]
cycle_degrees = sorted({tuple(x+y for x,y in zip(r,g))
                        for r,g in product(Rdegrees,Gdegrees)})
assert (1,1,1,1) not in cycle_degrees

# Full-twisting tensor needs complementary characters for a paired divisor.
assert all((j+4*j)%9 != 0 and (4*j+7*j)%9 != 0 and (j+7*j)%9 != 0
           for j in [1,2,4,5,7,8])

out = {
 'regular_differentials':hol,
 'N_size':len(N), 'annihilator':ann,
 'Y0_H3_dimension':len(survivors), 'C3_orbit_sizes':dict(Counter(map(len,orbits))),
 'Y_H3_by_p':dict(sorted(Y.items())), 'U_by_p':dict(sorted(U.items())),
 'old_by_p':dict(sorted(old.items())), 'normalizing_single_phases':normalizing,
 'M_size':len(M), 'degree_Y_to_Z':len(M)//len(N),
 'Arapura_Lminus8':Lminus8,'Arapura_inequality':[6*h3,len(survivors)],
 'T3':t3,'T9':t9,
 'generic_fiber_genera':{'Gamma3':1+(-2*27+3*6*9)//2,
                          'Gamma9_lift':1+(-2*9+3*18+3*36)//2},
 'Gamma9_Kunneth_degrees':cycle_degrees,
 'canonical_base_coefficient':str(-2+3*Fraction(8,9)+Fraction(2,3)),
 'verdict':'Exact identities only; both displayed cylinders have zero target projection.'}
print(json.dumps(out,indent=2))
