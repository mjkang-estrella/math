# v2_configs.py — stage-1 filter over all digit placements (positions 0..24),
# valid for L >= 26. For each placement (c-vector), compute t0 = v2(9S-1), then test
# joint solvability of:
#   (i)   3^A 7^B == (K/2^t0) * 9^-1  (mod 8)      -> parity class of (A,B)
#   (ii)  2^t0 3^A 7^B == 1 + c0    (mod 5)
#   (iii) 2^t0 3^A 7^B == S3 - 14   (mod 125),  S3 = c0 + 10 c1 + 100 c2
# A placement dies if no (A,B) with the (i)-parity satisfies (ii)&(iii).
# Also certifies the moduli facts used. Stdlib only.

PMAX = 25          # positions 0..24 explicit; digits beyond -> "high"
MOD2 = 1 << 25     # 2-adic working modulus (needs t0+3 <= 25 and L >= 25)

def v2(m):
    assert m != 0
    t = 0
    while m % 2 == 0:
        m //= 2; t += 1
    return t

def configs(ms):
    """All c-vectors of length PMAX with the multiset digits placed at distinct
    positions < PMAX (unused digits are 'high', positions >= PMAX)."""
    import itertools
    seen = set()
    for perm in set(itertools.permutations(ms)):
        for pos in itertools.combinations(range(PMAX), len(ms)):
            c = [0] * PMAX
            for d, p in zip(perm, pos):
                c[p] = d
            seen.add(tuple(c))
    return sorted(seen)

def odd_part_res(K, t0):
    """(K / 2^t0) * 9^-1 mod 8  (K/2^t0 odd)."""
    return ((K >> t0) * 9 % 8)  # 9 ≡ 1 mod 8, inverse of 9 mod 8 is 9? 9*9=81≡1 ✓

def stage1(c):
    S = sum(cp * 10**p for p, cp in enumerate(c))
    K = 9 * S - 1
    if K % MOD2 == 0:
        return ("DEEP", None)
    t0 = v2(K % MOD2) if K == 0 else v2(K)
    # careful: K computed from low positions only; true K ≡ this mod 2^25
    Kl = K % MOD2
    if Kl == 0:
        return ("DEEP", None)
    t0 = v2(Kl)
    O = odd_part_res(Kl, t0)          # 3^A 7^B ≡ O (mod 8)
    par = {1: (0, 0), 3: (1, 0), 5: (1, 1), 7: (0, 1)}[O]
    c0 = c[0]
    t5 = pow(2, t0, 5)
    tgt5 = (1 + c0) % 5
    S3 = (c[0] + 10 * c[1] + 100 * c[2]) % 125
    tgt125 = (S3 - 14) % 125
    sols = []
    for A in range(100):
        if A % 2 != par[0]:
            continue
        p3a = pow(3, A, 125)
        for B in range(20):
            if B % 2 != par[1]:
                continue
            v125 = t5 * p3a % 125 * pow(7, B, 125) % 125
            if v125 != tgt125:
                continue
            if t5 * pow(3, A, 5) * pow(7, B, 5) % 5 != tgt5:
                continue
            sols.append((A, B))
    return ("ALIVE" if sols else "DEAD", (t0, O, par, tgt5, tgt125, sols))

def main():
    # --- certification of the moduli facts used ---
    assert pow(9, -1, 8) == 9 % 8 or (9 * 9) % 8 == 1
    assert (9 * 14) % 125 == 1, "9^-1 mod 125"
    assert (9 * 4) % 5 == 1, "9^-1 mod 5"
    # R_L ≡ -9^-1 mod 2^k for L >= k (spot check)
    for L in (25, 26, 30):
        RL = (10**L - 1) // 9
        for k in (3, 8, 17, 25):
            if L >= k:
                assert (RL + pow(9, -1, 1 << k)) % (1 << k) == 0, (L, k)
    # 10^p ≡ 0 mod 2^k iff p >= k
    for p in range(30):
        for k in (3, 10, 25):
            assert (10**p) % (1 << k) == 0 if p >= k else (10**p) % (1 << k) != 0
    # ord_125(3) = 100, ord_125(7) = 20
    assert pow(3, 100, 125) == 1 and pow(3, 20, 125) != 1
    assert pow(7, 20, 125) == 1 and pow(7, 4, 125) != 1 and pow(7, 10, 125) != 1
    print("moduli facts OK")

    multisets = {"{2,2}": (1, 1), "{2,3}": (1, 2), "{2,4}": (1, 3),
                 "{3,3}": (2, 2), "{2,2,2}": (1, 1, 1)}
    survivors = []
    deep = []
    for name, ms in multisets.items():
        alive = 0
        for c in configs(ms):
            st, info = stage1(c)
            if st == "DEEP":
                deep.append((name, c))
            elif st == "ALIVE":
                alive += 1
                survivors.append((name, c, info))
        print(f"{name}: {alive} alive placements")
    print("DEEP:", len(deep))
    for d in deep[:10]:
        print("  DEEP", d[0], [i for i, v in enumerate(d[1]) if v])
    print("--- survivors ---")
    for name, c, info in survivors:
        pos = [(p, v) for p, v in enumerate(c) if v]
        t0, O, par, tgt5, tgt125, sols = info
        print(f"{name} digits at {pos}  t0={t0} O(mod8)={O} par(A,B)={par} "
              f"tgt5={tgt5} tgt125={tgt125} #ABclasses={len(sols)}")
        print("    AB classes (A mod 100, B mod 20):", sols[:24])

main()
