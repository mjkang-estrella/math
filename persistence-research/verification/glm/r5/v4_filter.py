#!/usr/bin/env python3
"""Round 5, v4: per-L necessary-condition filter for pairs/triples, L in [26, 6000].

Setup: n = R_L + S, S = sum c_p 10^p over the multiset's digits (c = digit-1),
9n = 10^L + K, K = 9S - 1, n = 2^t 3^A 7^B with t = v2(K) = v2(9S_low - 1)
(S_low = part of S at positions <= 10; far positions >= 11 do not change
K mod 2^11, K mod 5^11, n mod 10^11).

Necessary conditions checked per (essential config, stage-1 class (a0,b0) mod
(100,20), L):
  (N2) 2-adic coset: 3^A 7^B == (n_low/2^t) mod 2^(11-t). The kernel of
       (A,B)->3^A7^B contains (-d,2), d = dlog_3(49) mod 2^(11-t) (49 = 3^d,
       well posed since 49 = 1 mod 16), so A + (d/2)B == G (mod 2^(9-t)).
  (N3) size strip (10^L+K_lo)/(9*2^t) <= 3^A 7^B <= (10^L+K_hi)/(9*2^t),
       K_lo/K_hi from far digits at their lowest/highest positions.
  (N4) exact last-11-digit congruence 2^t 3^A 7^B == n_low (mod 10^min(L,11)).
Stage-1 classes: a0 + 55*b0 ≡ kappa (mod 100), kappa = dlog_3((9S_low-1) 2^-t 9^-1)
mod 5^11 (Lemma C; s ≡ 55 mod 100 certified). All arithmetic exact except float
logs in the strip, which carry ~1e-8 absolute error against 1e-6 margins; every
candidate that survives is re-verified by the exact (N4) power computation.
"""
import itertools, math, sys

MULTISETS = [(2,2), (2,3), (2,4), (3,3), (2,2,2)]
PMAX = 10                     # low positions 0..10; digits beyond are FAR
LMIN, LMAX = 26, 6000
LN2, LN3, LN7 = math.log(2), math.log(3), math.log(7)
P11 = 5**11
S_MOD = 55                    # dlog_3(7) mod 100, certified in v4_cert.txt

def dlog5(h):
    """dlog base 3 mod 5^11; 3 is primitive, h must be a unit."""
    ordg = 4 * 5**10
    m = math.isqrt(ordg) + 1
    tbl = {}; e = 1
    for j in range(m):
        tbl.setdefault(e, j); e = e * 3 % P11
    factor = pow(pow(3, m, P11), -1, P11)
    g = h % P11
    for i in range(m + 1):
        if g in tbl:
            x = i*m + tbl[g]
            assert pow(3, x, P11) == h % P11
            return x
        g = g * factor % P11
    raise ValueError("no dlog (h not a unit)")

def v2(x):
    if x == 0: return 10**9
    return (x & -x).bit_length() - 1

def build_coset(t, n_low):
    """(A mod 2^(9-t), B mod 2^(8-t)) with 3^A 7^B == n_low/2^t mod 2^(11-t)."""
    m = 11 - t; Mm = 1 << m
    odd = (n_low >> t) % Mm
    t3 = [pow(3, a, Mm) for a in range(1 << (m-2))]
    d7 = {}
    for b in range(1 << (m-3)):
        d7.setdefault(pow(7, b, Mm), []).append(b)
    coset = []
    for a, va in enumerate(t3):
        need = odd * pow(va, -1, Mm) % Mm
        coset.extend((a, b) for b in d7.get(need, ()))
    return coset

def essential_configs(delta):
    """All placements of the multiset's offsets into positions 0..10 or FAR.
    Returns dict (lowsig, far) -> (S_low, far_offsets), deduped."""
    offsets = sorted(delta)          # distinct offset values
    counts = [delta[o] for o in offsets]
    out = {}
    slots = list(range(PMAX+1)) + [None]  # None = FAR
    for assign in itertools.product(slots, repeat=len(offsets)):
        # positions must be distinct when a value has count 1... value with
        # count k may occupy k distinct slots; enforce injectivity on slots
        used = [s for s in assign if s is not None]
        if len(set(used)) != len(used): continue
        sig = [0]*(PMAX+1); far = []
        for o, s in zip(offsets, assign):
            if s is None: far.append(o)
            else: sig[s] += o   # offsets per multiset member; sum ok (distinct slots)
        # count-aware: offset value o with count>1 occupies multiple slots -
        # handled since assign has one entry per MEMBER? No: per distinct value.
        # Fix: expand members.
        out.setdefault((tuple(sig), tuple(sorted(far))), None)
    # redo properly, member-wise
    out = {}
    members = []
    for o, c in delta.items(): members += [o]*c
    for assign in itertools.product(slots, repeat=len(members)):
        used = [s for s in assign if s is not None]
        if len(set(used)) != len(used): continue
        sig = [0]*(PMAX+1); far = []
        for o, s in zip(members, assign):
            if s is None: far.append(o)
            else: sig[s] += o
        S_low = sum(sig[p] * 10**p for p in range(PMAX+1))
        out.setdefault((tuple(sig), tuple(sorted(far))), (S_low, sorted(far)))
    return sorted(out.values(), key=lambda x: (x[0], x[1]))

def main():
    dead = []; live_groups = 0; survivors = []
    for ms in MULTISETS:
        delta = {}
        for d in ms: delta[d-1] = delta.get(d-1, 0) + 1
        cfgs = essential_configs(delta)
        print(f"== {ms}: {len(cfgs)} essential configs ==", flush=True)
        for ci, (S_low, far) in enumerate(cfgs):
            tag = f"  c{ci} S_low={S_low} far={far}"
            Kt = (9*S_low - 1) % (1 << 11)
            if Kt == 0:
                dead.append((ms, S_low, far, "deep low (v2(9S-1) >= 11)")); continue
            t = v2(Kt)
            n_low = (11111111111 + S_low) % (10**11)
            if v2(n_low) != t:
                dead.append((ms, S_low, far, f"N0 v2(n_low)={v2(n_low)} != t={t}")); continue
            try:
                kap = dlog5((9*S_low - 1) % P11 * pow(2, -t, P11) % P11 * pow(9, -1, P11) % P11)
            except ValueError:
                dead.append((ms, S_low, far, "5 | K")); continue
            classes = [((kap - S_MOD*b0) % 100, b0) for b0 in range(20)]
            coset = build_coset(t, n_low)
            if not coset:
                dead.append((ms, S_low, far, "empty 2-adic coset")); continue
            m = 11 - t; Mm = 1 << m
            d = next(a for a in range(1 << (m-2)) if pow(3, a, Mm) == 49 % Mm)
            assert d % 4 == 0
            ch = d >> 1
            G = (coset[0][0] + ch*coset[0][1]) % (1 << (m-2))
            assert all((A + ch*B) % (1 << (m-2)) == G for A, B in coset)
            # class filter: A ≡ G - ch*B (mod M2); ch even => A mod 4 == G mod 4
            classes = [(a0, b0) for a0, b0 in classes if a0 % 4 == G % 4]
            if not classes:
                dead.append((ms, S_low, far, "no class meets 2-adic invariant")); continue
            live_groups += 1
            g_surv = []
            M2 = 1 << (m-2); Mcrt = M2 * 25
            istep = pow(M2 >> 2, -1, 25)
            for L in range(LMIN, LMAX+1):
                K_lo = K_hi = 9*S_low - 1
                fs = sorted(far)
                for i, c in enumerate(fs): K_lo += 9 * c * 10**(11+i)
                for i, c in enumerate(reversed(fs)): K_hi += 9 * c * 10**(L-1-i)
                num_lo = math.log(10**L + K_lo) - math.log(9) - t*LN2
                num_hi = math.log(10**L + K_hi) - math.log(9) - t*LN2
                A_max = int(num_hi / LN3) + 1
                mod = 10**min(L, 11); nl = n_low % mod
                pt = pow(2, t, mod)
                for a0, b0 in classes:
                    for A in range(a0 % 100, A_max+1, 100):
                        blo = (num_lo - A*LN3)/LN7
                        bhi = (num_hi - A*LN3)/LN7
                        if bhi < 0: break
                        lo = max(0, math.ceil(blo - 1e-6))
                        for B in (lo, lo+1):
                            if not (blo - 1e-6 <= B <= bhi + 1e-6): continue
                            if B % 20 != b0: continue
                            r2 = (G - ch*B) % M2
                            # A ≡ r2 (mod M2), A ≡ a0 (mod 100)
                            g4 = (a0 - r2) % 4
                            if g4: continue
                            k0 = (((a0 - r2) >> 2) * istep) % 25
                            Ac = r2 + M2*k0
                            if (A - Ac) % Mcrt: continue
                            if pt * pow(3, A, mod) % mod * pow(7, B, mod) % mod == nl:
                                g_surv.append((L, a0, b0, A, B))
            if g_surv:
                print(tag, f"SURVIVORS: {g_surv[:10]}")
                survivors.extend((ms, S_low, far)+s for s in g_surv)
            sys.stdout.flush()
        print(f"  -- {ms}: live groups so far {live_groups}, dead {len(dead)}", flush=True)
    print(f"\nTOTAL live groups: {live_groups}; dead records: {len(dead)}; survivors: {len(survivors)}")
    for s in survivors: print("SURVIVOR:", s)

if __name__ == '__main__':
    main()
