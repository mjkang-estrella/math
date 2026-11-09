#!/usr/bin/env python3
"""Round 5, v5: exact-integer cross-check of the v4 fast path.

For sampled (config, L), brute-force ALL (A, B) with
  (10^L+K_lo)/(9*2^t) <= 3^A 7^B <= (10^L+K_hi)/(9*2^t)
using EXACT integer comparisons only (no floats), and check the full
necessary-condition set: class membership (a0 mod 100, b0 mod 20 from the
5-adic pin mod 5^11), the 2-adic coset invariant A + (d/2)B ≡ G mod 2^(9-t),
and the exact congruence 2^t 3^A 7^B ≡ n_low mod 10^min(L,11).
Agreement with v4 (empty survivor set) validates the fast path.
"""
import math, random, sys
sys.path.insert(0, '.')
from v4_filter import (dlog5, v2, build_coset, essential_configs, P11, S_MOD,
                       PMAX)

def ilog(x, b):
    lo, hi = 0, 1
    while b**hi <= x: hi *= 2
    lo = hi >> 1
    while lo + 1 < hi:
        mid = (lo+hi) >> 1
        if b**mid <= x: lo = mid
        else: hi = mid
    return lo

def ceil_log(x, b):
    if x <= 1: return 0
    f = ilog(x, b)
    return f if b**f == x else f + 1

def exact_filter(ms, S_low, far, L):
    delta = {}
    for d in ms: delta[d-1] = delta.get(d-1, 0) + 1
    Kt = (9*S_low - 1) % (1 << 11)
    if Kt == 0: return None  # deep low: skipped in v4 too
    t = v2(Kt)
    n_low = (11111111111 + S_low) % (10**11)
    if v2(n_low) != t: return []
    kap = dlog5((9*S_low-1) % P11 * pow(2,-t,P11) % P11 * pow(9,-1,P11) % P11)
    classes = [((kap - S_MOD*b0) % 100, b0) for b0 in range(20)]
    coset = build_coset(t, n_low)
    if not coset: return []
    m = 11 - t; Mm = 1 << m
    d = next(a for a in range(1 << (m-2)) if pow(3, a, Mm) == 49 % Mm)
    ch = d >> 1
    G = (coset[0][0] + ch*coset[0][1]) % (1 << (m-2))
    classes = [(a0,b0) for a0,b0 in classes if a0 % 4 == G % 4]
    if not classes: return []
    K_lo = K_hi = 9*S_low - 1
    fs = sorted(far)
    for i, c in enumerate(fs): K_lo += 9*c*10**(11+i)
    for i, c in enumerate(reversed(fs)): K_hi += 9*c*10**(L-1-i)
    mod = 10**min(L, 11); nl = n_low % mod
    pt = pow(2, t, mod)
    found = []
    # A range: 9*2^t*3^A*7^B >= 10^L+K_lo with B>=0 => 3^A <= (10^L+K_hi)/(9*2^t)
    A_hi = ilog((10**L + K_hi) // (9 * 2**t), 3) + 1
    for A in range(0, A_hi+1):
        p3 = 9 * 2**t * 3**A
        # B range: 7^B in [ (10^L+K_lo)/p3 , (10^L+K_hi)/p3 ]
        Blo = ceil_log((10**L + K_lo + p3 - 1)//p3, 7)  # ceil of quotient
        Bhi = ilog((10**L + K_hi)//p3, 7)
        for B in range(Blo, Bhi+1):
            v = p3 * 7**B
            if not (10**L + K_lo <= v <= 10**L + K_hi): continue
            if (A - G + ch*B) % (1 << (m-2)): continue
            if not any(A % 100 == a0 and B % 20 == b0 for a0, b0 in classes): continue
            if pt * pow(3, A, mod) % mod * pow(7, B, mod) % mod == nl:
                found.append((A, B))
    return found

def main():
    random.seed(5)
    mismatches = 0; checked = 0
    for ms in [(2,2),(2,3),(2,4),(3,3),(2,2,2)]:
        delta = {}
        for d in ms: delta[d-1] = delta.get(d-1, 0) + 1
        cfgs = essential_configs(delta)
        sample = random.sample(cfgs, min(6, len(cfgs)))
        for S_low, far in sample:
            for L in (100, 137, 500):
                r = exact_filter(ms, S_low, far, L)
                if r is None: continue
                checked += 1
                if r:
                    print("NONEMPTY exact:", ms, S_low, far, L, r[:5])
        print(f"{ms}: sampled {len(sample)} configs x 3 L done", flush=True)
    print(f"exact cross-checks run: {checked}; all survivor sets empty unless printed")

main()
