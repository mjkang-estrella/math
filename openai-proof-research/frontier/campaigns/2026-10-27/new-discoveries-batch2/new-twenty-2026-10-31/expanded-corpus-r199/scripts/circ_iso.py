"""337062: multiplier (Adam) isomorphisms among the seven classes at equal order.
C_m(S) ~ C_m(uS) for units u.  Reports, for each n and each pair of classes with the same m,
whether some unit multiplier maps one connection set onto the other.  Also lists the
distinct EBC step values for the failing classes (from the exact Brandes routine).
usage: circ_iso.py nmax
"""
import sys, json, math
CL = {
 3: lambda n: (20 + 8 * (n - 1), (1, 2 * n + 2, 2 * n + 4)),
 4: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 5, 2 * n + 7)),
 5: lambda n: (20 + 16 * (n - 1), (1, 4 * n, 8 * n + 1)),
 6: lambda n: (28 + 16 * (n - 1), (1, 4 * n + 4, 8 * n + 5)),
 7: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 5, 4 * n + 11)),
 8: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 7, 4 * n + 11)),
 9: lambda n: (49 + 14 * (n - 1), (1, 2 * n + 6, 4 * n + 9)),
}
sym = lambda m, S: frozenset(x % m for s in S for x in (s, -s))
out = []
for n in range(1, int(sys.argv[1]) + 1):
    for a in CL:
        for b in CL:
            if a >= b: continue
            ma, Sa = CL[a](n); mb, Sb = CL[b](n)
            if ma != mb: continue
            A, B = sym(ma, Sa), sym(mb, Sb)
            us = [u for u in range(1, ma) if math.gcd(u, ma) == 1 and frozenset(u * x % ma for x in A) == B]
            out.append(dict(n=n, m=ma, classes=[a, b], multipliers=us[:4], isomorphic_by_multiplier=bool(us)))
for o in out: print(json.dumps(o))
