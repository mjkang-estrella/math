# r4/v2_brute.py — exhaustive cross-check of the odd-layer theorem for L <= 1500.
# For every (delta, L, e) in range, test whether 9n = 10^L + 9(delta-1)*10^e - 1 is
# 2^t*3^a*7^b (t>0 exactly for the even layer e=0, even delta; the odd layer needs t=0,
# which is asserted separately).
# Run: bash -c 'ulimit -v 3000000; python3 -I verification/glm/r4/v2_brute.py'
import sys

LMAX = 1500
DELTAS = [2, 3, 4, 6, 7, 8, 9]
members = []   # (delta, L, e, n)

for L in range(1, LMAX + 1):
    p10L = 10**L
    p10e = 1
    for e in range(0, L):
        for d in DELTAS:
            m = p10L + 9 * (d - 1) * p10e - 1
            mm = m
            while mm % 2 == 0: mm //= 2
            while mm % 3 == 0: mm //= 3
            while mm % 7 == 0: mm //= 7
            if mm == 1:
                members.append((d, L, e, m // 9))
        p10e *= 10

# known full member lists (even layer from round 3b + odd layer)
known = {
    2: {2: (1,0), 12: (2,0), 21: (2,1), 112: (3,0)},
    3: {3: (1,0)},
    4: {4: (1,0), 14: (2,0)},
    6: {6: (1,0), 16: (2,0)},
    7: {7: (1,0)},
    8: {8: (1,0), 18: (2,0), 81: (2,1)},
    9: {9: (1,0)},
}
got = {}
for d, L, e, n in members:
    got.setdefault(d, {})[n] = (L, e)

ok = True
# odd-layer consistency: for odd n (e>=1 with even delta; any e with odd delta), 9n must
# have NO factor 2 — recheck those with the pure 3^a*7^b test
for d, L, e, n in members:
    odd_case = (e >= 1) if d in (2,4,6,8) else True
    if odd_case:
        m = 9 * n
        assert m % 2 == 1, (d, L, e, n)
        while m % 3 == 0: m //= 3
        while m % 7 == 0: m //= 7
        assert m == 1, (d, L, e, n)
for d in DELTAS:
    exp = known[d]
    g = got.get(d, {})
    if g != exp:
        ok = False
        print(f"MISMATCH delta={d}: got {g}, expected {exp}")
print("members found:", [(d, n) for d, ns in got.items() for n in ns])
print("EXHAUSTIVE CHECK L<=%d: %s" % (LMAX, "PASS — member lists exactly as known" if ok else "FAIL"))
sys.exit(0 if ok else 1)
