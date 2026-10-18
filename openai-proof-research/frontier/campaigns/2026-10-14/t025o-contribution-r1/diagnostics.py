#!/usr/bin/env python3
"""MIT. Exact finite bookkeeping checks for the T025O54 contribution review.

Checks (exact rationals, fixed seed): the four odd base-5 terminal templates;
the equivalence of the constrained residue condition (z = 1 mod 2l, 0 <= uz-Qt < delta*u)
with {Qt/(2lu)} in ((1-delta)/(2l), 1/(2l)]; and that one residue step for nu=1 is
the nu=0 step with every denominator multiplied by l. Writes nothing.
These finite checks certify no asymptotic statement.
"""
from fractions import Fraction as F
import json, math, random

def main():
    out = {}
    T = {1: [7], 2: [7, 9, 33, 693], 3: [3, 11, 231], 4: [3, 7, 11, 231]}
    out['templates'] = all(sum(F(1, x) for x in T[d]) == F(d, 7) and len(set(T[d])) == len(T[d])
                           and all(x % 2 and x % 5 for x in T[d]) for d in T)
    rng = random.Random(20261018)
    bad = n = 0
    for _ in range(20000):
        l = rng.choice([13, 17, 19, 23]); u = rng.randint(2, 400); Q = rng.randint(1, 50)
        t = rng.randint(u, 5000); delta = F(rng.randint(1, 9), 10)
        direct = any(0 <= u * z - Q * t < delta * u for z in range(1, Q * t // u + 3) if z % (2 * l) == 1)
        x = F(Q * t, 2 * l * u); fr = x - math.floor(x)
        crit = (F(1, 2 * l) - delta / (2 * l)) < fr <= F(1, 2 * l)
        n += 1; bad += direct != crit
    out['residue_equivalence'] = {'cases': n, 'mismatches': bad}
    mm = 0
    for _ in range(5000):
        l = rng.choice([13, 17]); M0 = 7 * 5 ** 3 * 101; t = rng.choice([1, 101]); Q = rng.choice([1, 3 ** 5])
        u = rng.randint(1, 999)
        z = math.ceil(Q * t / u); z += (1 - z) % (2 * l); h = u * z - Q * t
        for nu in (0, 1):
            lhs = F(u, l ** nu * M0 * Q)
            rhs = F(1, (l ** nu * M0 // t) * z) + F(h, z * l ** nu * M0 * Q)
            mm += lhs != rhs
        mm += (l * M0 // t) * z != l * ((M0 // t) * z)
        mm += z % 2 == 0 or z % l == 0
    out['scaling_identity_mismatches'] = mm
    print(json.dumps(out, sort_keys=True))

if __name__ == '__main__':
    main()
