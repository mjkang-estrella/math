#!/usr/bin/env python3
"""v2_lifting.py -- verify the lifting structure of v_p(10^L + c).

 (F1) ord_{3^k}(10) = 3^(k-2) for 2 <= k <= 15, and v3(10^m - 1) = 2 + v3(m), 1<=m<=3000.
 (F2) ord_{7^k}(10) = 6*7^(k-1) for 1 <= k <= 10, and v7(10^6 - 1) = 1.
 (F3) For each delta, c = 9*delta-10: solutions of 10^x ≡ -c (mod 3^K), K>=3, form ONE
      class x ≡ λ_K mod 3^(K-2) (or empty); mod 7^K, K>=1: one class μ_K mod 6*7^(K-1)
      (or empty); λ_K ≡ ℓ mod 3, μ_K ≡ r mod 6 (nested).
 (F4) For all 1 <= L <= 20000:  3^K | 10^L+c  <=>  L ≡ λ_K (mod 3^(K-2))  (λ_K defined);
      7^K | 10^L+c <=> L ≡ μ_K (mod 6*7^(K-1)) (μ_K defined).
 (F5) Whenever a = v3(10^L+c) > 2 + log3(L) then L = λ_a; whenever b > 1 + log7(L)
      then L = μ_b.  (These are exactly the j=0 "fixed point" cases.)
"""
CS = {2: 8, 4: 26, 6: 44, 8: 62}
LMAX = 20000

def vp(N, p):
    k = 0
    while N % p == 0:
        N //= p; k += 1
    return k

def main():
    ok = True
    # F1
    f1 = True
    for k in range(2, 16):
        mod = 3**k; ordv = 1; x = 10 % mod
        while x != 1:
            x = x * 10 % mod; ordv += 1
        if ordv != 3**(k-2): print(f"F1 FAIL ord_(3^{k})={ordv}"); f1 = False
    for m in range(1, 3001):
        if vp(10**m - 1, 3) != 2 + vp(m, 3):
            print(f"F1 FAIL LTE at m={m}"); f1 = False; break
    print("F1 OK" if f1 else "F1 FAIL"); ok &= f1
    # F2
    f2 = True
    for k in range(1, 11):
        mod = 7**k; ordv = 1; x = 10 % mod
        while x != 1:
            x = x * 10 % mod; ordv += 1
        if ordv != 6 * 7**(k-1): print(f"F2 FAIL ord_(7^{k})={ordv}"); f2 = False
    if vp(10**6 - 1, 7) != 1: print("F2 FAIL v7(10^6-1)"); f2 = False
    print("F2 OK" if f2 else "F2 FAIL"); ok &= f2

    for d, c in CS.items():
        # lambda_K
        lam = {}; K = 3; prev = None
        while K <= 60:
            mod = 3**K
            if prev is None:
                cands = [x for x in range(3) if pow(10, x, 27) == (-c) % 27]
            else:
                step = 3**(K-3)
                cands = [prev + j*step for j in range(3)
                         if pow(10, (prev + j*step) % 3**(K-2), mod) == (-c) % mod]
            if not cands: break
            prev = lam[K] = cands[0] % 3**(K-2); K += 1
        lam_max = K - 1
        # mu_K
        mu = {}; K = 1; prev = None
        while K <= 25:
            mod = 7**K
            if prev is None:
                cands = [x for x in range(6) if pow(10, x, 7) == (-c) % 7]
            else:
                step = 6 * 7**(K-2)
                cands = [prev + j*step for j in range(7)
                         if pow(10, (prev + j*step) % (6*7**(K-1)), mod) == (-c) % mod]
            if not cands: break
            prev = mu[K] = cands[0] % (6*7**(K-1)); K += 1
        mu_max = K - 1
        ell = lam[3] % 3 if 3 in lam else None
        r = mu[1] % 6 if 1 in mu else None
        print(f"delta={d}: lambda K=3..{lam_max}, mu K=1..{mu_max}, ell={ell}, r={r}")
        f3 = True
        for K in range(4, lam_max+1):
            if lam[K] % 3 != ell: print(f" F3 FAIL lam_{K}%3"); f3 = False
        for K in range(2, mu_max+1):
            if mu[K] % 6 != r: print(f" F3 FAIL mu_{K}%6"); f3 = False
        ok &= f3
        # F4 + F5 sweep
        viol = 0
        aexc = []; bexc = []
        for L in range(1, LMAX+1):
            N = 10**L + c
            a = vp(N, 3); b = vp(N, 7)
            for K in range(3, lam_max+1):
                if (a >= K) != (L % 3**(K-2) == lam[K]): viol += 1
            for K in range(1, mu_max+1):
                if (b >= K) != (L % (6*7**(K-1)) == mu[K]): viol += 1
            if a >= 3 and 3**a > 9*L and L >= 2: aexc.append((L, a))
            if b >= 2 and 7**b > 7*L and L >= 2: bexc.append((L, b))
        f45 = viol == 0
        for (L, a) in aexc:
            if L != lam.get(a): print(f" F5 FAIL a-exc d={d} L={L} a={a} lam_a={lam.get(a)}"); f45 = False
        for (L, b) in bexc:
            if L != mu.get(b): print(f" F5 FAIL b-exc d={d} L={L} b={b} mu_b={mu.get(b)}"); f45 = False
        print(f"  F4 congruence violations: {viol}; a-exc pairs {aexc}; b-exc pairs {bexc}")
        print(f"  F4/F5 {'OK' if f45 else 'FAIL'}")
        ok &= f45
    print("ALL LIFTING CHECKS PASSED" if ok else "FAILURES FOUND")

if __name__ == "__main__":
    main()
