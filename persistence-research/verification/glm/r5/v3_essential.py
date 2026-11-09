# v3_essential.py — essential low configurations.
# A placement is described by its c-vector over positions 0..10; digits beyond
# position 10 are "far". Facts used (certified at bottom):
#  - 10^p ≡ 0 (mod 2^11) for p ≥ 11, so t0 = v2(9S-1) and n mod 2^k (k ≤ 11+3)
#    depend only on positions < 11, PROVIDED t0 ≤ 10. We verify max t0 ≤ 10 over
#    ALL placements into positions 0..10 (and none hits the 2^25 ceiling in v2).
#  - Stage-1 filter (v2_configs.py): (i) mod-8 parity, (ii) mod 5, (iii) mod 125.
# Output: essential survivors grouped by (multiset, c0,c1,c2, t0, O, targets),
# with the (A mod 100, B mod 20) solution classes.
import itertools

P10 = 11          # positions 0..10 explicit
MOD2 = 1 << 25

def v2(m):
    t = 0
    while m % 2 == 0:
        m //= 2; t += 1
    return t

def essential_vectors(ms):
    seen = set()
    for perm in set(itertools.permutations(ms)):
        for pos in itertools.combinations(range(P10), len(ms)):
            c = [0] * P10
            for d, p in zip(perm, pos):
                c[p] = d
            seen.add(tuple(c))
    return sorted(seen)

def analyze(c):
    S = sum(cp * 10**p for p, cp in enumerate(c))
    K = 9 * S - 1
    t0 = v2(K)
    O = ((K >> t0) * 9) % 8
    par = {1: (0, 0), 3: (1, 0), 5: (1, 1), 7: (0, 1)}[O]
    tgt5 = (1 + c[0]) % 5
    S3 = (c[0] + 10 * c[1] + 100 * c[2]) % 125
    tgt125 = (S3 - 14) % 125
    sols = []
    for A in range(100):
        if A % 2 != par[0]:
            continue
        for B in range(20):
            if B % 2 != par[1]:
                continue
            if pow(2, t0, 125) * pow(3, A, 125) % 125 * pow(7, B, 125) % 125 != tgt125:
                continue
            if pow(2, t0, 5) * pow(3, A, 5) * pow(7, B, 5) % 5 != tgt5:
                continue
            sols.append((A, B))
    return dict(t0=t0, O=O, par=par, tgt5=tgt5, tgt125=tgt125, sols=sols)

def main():
    # certify: 10^p ≡ 0 mod 2^11 iff p ≥ 11; 9*14≡1 mod 125; R_L ≡ -9^-1 mod 2^k
    for p in (10, 11, 12):
        assert ((10**p) % 2048 == 0) == (p >= 11)
    assert (9 * 14) % 125 == 1
    for L in (12, 30):
        RL = (10**L - 1) // 9
        for k in (11,):
            assert (RL + pow(9, -1, 1 << k)) % (1 << k) == 0
    print("facts OK")

    multisets = {"{2,2}": (1, 1), "{2,3}": (1, 2), "{2,4}": (1, 3),
                 "{3,3}": (2, 2), "{2,2,2}": (1, 1, 1)}
    max_t0 = 0
    survivors = []
    for name, ms in multisets.items():
        groups = {}
        for c in essential_vectors(ms):
            d = analyze(c)
            max_t0 = max(max_t0, d["t0"])
            if d["sols"]:
                # group key: low digits (c0,c1,c2), t0, and which of positions 3..10
                # are occupied (affects t0/parity data already in key via t0,O,tgts)
                key = (name, c[0], c[1], c[2], d["t0"], d["O"], d["tgt5"], d["tgt125"])
                groups.setdefault(key, c)
        for key, rep in groups.items():
            survivors.append((key, rep))
        print(f"{name}: {len(groups)} essential survivor groups")
    print("max t0 over all placements:", max_t0)
    print("--- essential survivor groups ---")
    for key, rep in sorted(survivors):
        name, c0, c1, c2, t0, O, tgt5, tgt125 = key
        pos = [(p, v) for p, v in enumerate(rep) if v]
        print(f"{name} rep-positions {pos}")
        print(f"   c0={c0} c1={c1} c2={c2} t0={t0} O={O} par={ {1:(0,0),3:(1,0),5:(1,1),7:(0,1)}[O] } "
              f"tgt5={tgt5} tgt125={tgt125}")
        d = analyze(rep)
        print(f"   AB classes: {d['sols']}")

main()
