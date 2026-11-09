#!/usr/bin/env python3
"""v1_small.py -- brute force + exact valuations for 10^L + c_delta, even delta.

Checks, for each delta in {2,4,6,8} (c = 9*delta-10):
  (a) all L in [1, LMAX] with 10^L + c = 2^t 3^a 7^b (7-smooth), exact cofactor test;
  (b) the hand values of t(L) = v2(10^L+c);
  (c) residue conditions: a >= 3 iff L ≡ ℓ mod 3 ; b >= 1 iff L ≡ r mod 6;
  (d) growth: a <= 2 + log3(L) EXCEPT when L = lambda_a (exception, checked in v2);
      here we just record where a > 2 + ceil(log3 L) - 1 ... simpler: record all
      (L, a, b) with a > 2 + log3(L) or b > 1 + log7(L) for cross-check with v2.
"""
import sys
from math import log

LMAX = 5000
CS = {2: 8, 4: 26, 6: 44, 8: 62}

def vp(N, p):
    k = 0
    while N % p == 0:
        N //= p; k += 1
    return k, N

def main():
    ok = True
    for d, c in CS.items():
        sols = []
        t_viol = []
        a_res_viol = []   # a>=3 iff L ≡ ell mod 3
        b_res_viol = []
        agrowth = []      # (L,a) with a > 2 + floor(log3 L)  (candidates for exceptions)
        bgrowth = []
        ell = None; r = None
        # determine ell: a>=3 iff 3^3 | 10^L+c iff 10^L ≡ -c mod 27
        for L in range(1, 4):
            if (pow(10, L, 27) - (-c % 27)) % 27 == 0:
                ell = L % 3
        for L in range(1, 40):
            if (pow(10, L, 7) - (-c % 7)) % 7 == 0:
                r = L % 6
        assert ell is not None and r is not None
        for L in range(1, LMAX + 1):
            N = 10**L + c
            t, N = vp(N, 2)
            a, N = vp(N, 3)
            b, N = vp(N, 7)
            if N == 1:
                sols.append((L, t, a, b))
            # t formula check
            if L == 1: t_exp = {2:1,4:2,6:1,8:3}[d]
            elif L == 2: t_exp = {2:2,4:1,6:4,8:1}[d]
            elif L == 3: t_exp = {2:4,4:1,6:2,8:1}[d]
            else: t_exp = {2:3,4:1,6:2,8:1}[d]
            if t != t_exp:
                t_viol.append((L, t, t_exp))
            # residue conditions
            if (a >= 3) != (L % 3 == ell):
                a_res_viol.append((L, a))
            if (b >= 1) != (L % 6 == r):
                b_res_viol.append((L, b))
            # growth exceptions
            if a > 2 + log(L, 3) - 1e-12:
                agrowth.append((L, a))
            if b > 1 + log(L, 7) - 1e-12:
                bgrowth.append((L, b))
        print(f"delta={d} c={c}: ell={ell} (a>=3 iff L≡{ell} mod 3), r={r} (b>=1 iff L≡{r} mod 6)")
        print(f"  7-smooth solutions (L,t,a,b): {sols}")
        print(f"  t-formula violations: {t_viol[:5]} (count {len(t_viol)})")
        print(f"  a-residue violations: {a_res_viol[:5]} (count {len(a_res_viol)})")
        print(f"  b-residue violations: {b_res_viol[:5]} (count {len(b_res_viol)})")
        print(f"  a > 2+log3(L) at (L,a): {agrowth[:8]} ... count {len(agrowth)}")
        print(f"  b > 1+log7(L) at (L,b): {bgrowth[:8]} ... count {len(bgrowth)}")
        if t_viol or a_res_viol or b_res_viol:
            ok = False
    print("ALL CHECKS PASSED" if ok else "FAILURES FOUND")

if __name__ == "__main__":
    main()
