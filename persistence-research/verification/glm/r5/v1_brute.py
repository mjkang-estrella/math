# v1_brute.py — raw sweep: all 7-smooth n with digit multisets {2,2},{2,3},{2,4},{3,3} (pairs)
# and {2,2,2} (triples). n = R_L + sum c_p 10^p, c_p = digit-1. n 7-smooth iff
# 9n = 10^L - 1 + sum 9 c_p 10^p is 7-smooth. Stdlib only.
import itertools, sys

def smooth7(m):
    for p in (2, 3, 7):
        while m % p == 0:
            m //= p
    return m == 1

def factor(m):
    f = {}
    for p in (2, 3, 7):
        while m % p == 0:
            m //= p
            f[p] = f.get(p, 0) + 1
    assert m == 1
    return f

MULTISETS = [(1, 1), (1, 2), (1, 3), (2, 2), (1, 1, 1)]
LMAX = {3: 200, 2: 500}[2]  # placeholder

def sweep(multiset, Lmax):
    out = []
    pw = [10 ** i for i in range(Lmax + 1)]
    R = 0
    for L in range(1, Lmax + 1):
        R = R * 10 + 1
        if L < len(multiset):
            continue
        base = pw[L] - 1  # 10^L - 1
        for positions in itertools.combinations(range(L), len(multiset)):
            for perm in sorted(set(itertools.permutations(multiset))):
                m = base
                for c, p in zip(perm, positions):
                    m += 9 * c * pw[p]
                if smooth7(m):
                    f = factor(m)
                    out.append((multiset, L, positions, perm, m // 9, f))
    return out

def main():
    pairs_L, trip_L = 500, 200
    all_members = []
    for ms in [(1, 1), (1, 2), (1, 3), (2, 2)]:
        r = sweep(ms, pairs_L)
        print(f"multiset offsets {ms}: {len(r)} members up to L={pairs_L}")
        for x in r:
            print("   ", x)
        all_members += r
    r = sweep((1, 1, 1), trip_L)
    print(f"multiset offsets (1,1,1): {len(r)} members up to L={trip_L}")
    for x in r:
        print("   ", x)
    all_members += r
    print("TOTAL", len(all_members))

main()
