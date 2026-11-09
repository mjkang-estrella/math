#!/usr/bin/env python3
"""v3_close.py -- machine certificate for every arithmetic fact used in the
closing argument (notes/proof_attempt_glm_r3.md, section 3).

Facts:
 (C1) c = 9*delta-10 ≡ 8 (mod 9), so a = v3(10^L+c) >= 2 for ALL L (10^L ≡ 1 mod 9).
 (C2) -c mod 27 = 10^ell with ell = (2,0,1,2)[delta]; ord_27(10)=3, so
      a >= 3 <=> L ≡ ell (mod 3).
 (C3) 7 | 10^L+c <=> L ≡ r (mod 6), r = (3,2,5,0)[delta].
 (C4) ell mod 3 != r mod 3 for every delta  =>  a-exc and b-exc cannot co-occur,
      and each of them forces the other prime's valuation to its floor
      (a-exc => b=0 ; b-exc => a=2).
 (C5) t <= 3 for L >= 4 and the t-table; and 2^{L-s}5^L + c'' form:
      delta=2: s=3, c''=1 (L>=4); delta=4: s=1, c''=13 (L>=2);
      delta=6: s=2, c''=11 (L>=3); delta=8: s=1, c''=31 (L>=2).
 (C6) Size bound: 10^L >= 504*L^2 for all L >= 4 (504 = 8*63), and
      10^L/L^2 is strictly increasing for L >= 1.
 (C7) log_3(10) < 21/10 exactly: 3^21 > 10^10.
 (C8) 4*5^(L-1) > 21L/10 for all L >= 2, and (4*5^(L-1))/L is increasing.
 (C9) ord_{5^k}(3) = 4*5^(k-1) for 1 <= k <= 8.
 (C10) mod-16/8 valuation facts:
      a ≡ 1 (mod 4) => 3^a ≡ 3 (mod 16); a ≡ 0 (mod 4) => 3^a ≡ 1 (mod 16);
      3^a ≡ 3 (mod 16) => v2(3^a - 13) = 1 ; 3^a ≡ 1 (mod 16) =>
      v2(3^a - 11) = 1 and v2(3^a - 31) = 1 ;
      b even => 7^b ≡ 1 (mod 16) ; b odd => 7^b ≡ 7 (mod 8) ;
      v2(9*7^b - 1) = 3 for b even ; v2(9*7^b - 13) = 1 for b odd ;
      v2(9*7^b - 11) = 1 for b even ; v2(9*7^b - 31) = 1 for b even.
 (C11) mod-5 residue maps (discrete logs base 3 / 7 composed with 9, mod 5):
      delta=2 a-exc: 3^a ≡ 1 (mod 5) <=> 4 | a.
      delta=4 a-exc: 3^a ≡ 13 (mod 5) <=> a ≡ 1 (mod 4).
      delta=6 a-exc: 3^a ≡ 11 (mod 5) <=> 4 | a.
      delta=8 a-exc: 3^a ≡ 31 (mod 5) <=> 4 | a.
      delta=2 b-exc: 9*7^b ≡ 1 (mod 5) <=> b ≡ 2 (mod 4).
      delta=4 b-exc: 9*7^b ≡ 13 (mod 5) <=> b ≡ 1 (mod 4).
      delta=6 b-exc: 9*7^b ≡ 11 (mod 5) <=> b ≡ 2 (mod 4).
      delta=8 b-exc: 9*7^b ≡ 31 (mod 5) <=> b ≡ 2 (mod 4).
 (C12) STRUCTURAL SWEEP over L <= 20000, all delta: with a=v3(10^L+c), b=v7(10^L+c),
      lam/mu from v2:
        3^a > 9L      =>  L = lam[a]                     (a-exc)
        7^b > 7L      =>  L = mu[b]                      (b-exc)
        otherwise     =>  3^a * 7^b <= 63*L^2
        a-exc         =>  b = 0 and L ≡ ell (mod 3)
        b-exc         =>  a = 2 and L ≡ r (mod 6)
"""
CS = {2: 8, 4: 26, 6: 44, 8: 62}
ELL = {2: 2, 4: 0, 6: 1, 8: 2}
R   = {2: 3, 4: 2, 6: 5, 8: 0}
S_C = {2: (3, 1, 4), 4: (1, 13, 2), 6: (2, 11, 3), 8: (1, 31, 2)}  # delta -> (s, c'', Lmin)
LMAX = 20000

def vp(N, p):
    k = 0
    while N % p == 0:
        N //= p; k += 1
    return k

def lam_mu(d):
    c = CS[d]
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
    return lam, mu

def main():
    ok = True
    def chk(cond, msg):
        nonlocal ok
        if not cond:
            ok = False; print("FAIL:", msg)
    # C1
    for d, c in CS.items():
        chk(c % 9 == 8, f"C1 c_{d} mod 9")
        for L in range(1, 200):
            chk((10**L + c) % 9 == 0, f"C1 9|10^{L}+c d={d}")
    print("C1 ok" if ok else "C1 FAIL")
    # C2
    for d, c in CS.items():
        ell = ELL[d]
        chk(pow(10, ell, 27) == (-c) % 27, f"C2 10^{ell} = -c mod 27, d={d}")
        for x in range(27):
            if pow(10, x, 27) == (-c) % 27:
                chk(x % 3 == ell, f"C2 class x={x} d={d}")
    print("C2 ok" if ok else "C2 FAIL")
    # C3
    for d, c in CS.items():
        r = R[d]
        for L in range(1, 200):
            chk(((10**L + c) % 7 == 0) == (L % 6 == r), f"C3 d={d} L={L}")
    print("C3 ok" if ok else "C3 FAIL")
    # C4
    for d in CS:
        chk(ELL[d] % 3 != R[d] % 3, f"C4 d={d}")
    print("C4 ok" if ok else "C4 FAIL")
    # C5
    for d, c in CS.items():
        s, cpp, Lmin = S_C[d]
        for L in range(Lmin, Lmin + 50):
            N = 10**L + c
            t = vp(N, 2)
            chk(t == s and N == 2**s * (2**(L-s) * 5**L + cpp), f"C5 d={d} L={L}")
    # t <= 3 for L >= 4
    for d, c in CS.items():
        for L in range(4, 300):
            chk(vp(10**L + c, 2) <= 3, f"C5 t<=3 d={d} L={L}")
    print("C5 ok" if ok else "C5 FAIL")
    # C6
    chk(10**4 >= 504 * 16, "C6 base")
    for L in range(1, 200):
        chk(10 * L * L > (L+1)*(L+1), f"C6 monotone L={L}")
    for L in range(4, 60):
        chk(10**L >= 504 * L * L, f"C6 10^L>=504L^2 L={L}")
    print("C6 ok" if ok else "C6 FAIL")
    # C7
    chk(3**21 > 10**10, "C7")
    print("C7 ok" if ok else "C7 FAIL")
    # C8: 10*4*5^(L-1) > 21L for L>=2 and increasing
    chk(40 * 5**1 > 21 * 2, "C8 base")   # L=2: 4*5=20 > 4.2
    for L in range(2, 200):
        chk(10 * 4 * 5**(L-1) > 21 * L, f"C8 L={L}")
    for L in range(2, 100):
        chk(4 * 5**(L+1-1) * L > 4 * 5**(L-1) * (L+1), f"C8 mono L={L}")
    print("C8 ok" if ok else "C8 FAIL")
    # C9
    for k in range(1, 9):
        mod = 5**k; ordv = 1; x = 3 % mod
        while x != 1:
            x = x * 3 % mod; ordv += 1
        chk(ordv == 4 * 5**(k-1), f"C9 k={k}")
    print("C9 ok" if ok else "C9 FAIL")
    # C10
    for a in range(0, 33):
        p3 = pow(3, a, 16)
        if a % 4 == 1: chk(p3 == 3, f"C10 3^a mod16 a={a}")
        if a % 4 == 0: chk(p3 == 1, f"C10 3^a mod16 a={a}")
    for a in range(1, 34, 4):
        chk(vp(3**a - 13, 2) == 1, f"C10 v2(3^a-13) a={a}")
    for a in range(4, 65, 4):
        chk(vp(3**a - 11, 2) == 1, f"C10 v2(3^a-11) a={a}")
        chk(vp(3**a - 31, 2) == 1, f"C10 v2(3^a-31) a={a}")
    for b in range(0, 33):
        p7 = pow(7, b, 16)
        if b % 2 == 0: chk(p7 == 1, f"C10 7^b mod16 b={b}")
        else: chk(pow(7, b, 8) == 7, f"C10 7^b mod8 b={b}")
    for b in range(0, 33, 2):
        chk(vp(9 * 7**b - 1, 2) == 3, f"C10 v2(9*7^b-1) b={b}")
        chk(vp(9 * 7**b - 11, 2) == 1, f"C10 v2(9*7^b-11) b={b}")
        chk(vp(9 * 7**b - 31, 2) == 1, f"C10 v2(9*7^b-31) b={b}")
    for b in range(1, 34, 2):
        chk(vp(9 * 7**b - 13, 2) == 1, f"C10 v2(9*7^b-13) b={b}")
    print("C10 ok" if ok else "C10 FAIL")
    # C11
    def res_set(base, m, mod=5):
        return {pow(base, a, mod) * (m % mod) % mod: a % 4 for a in range(4)}
    # a-exc: 3^a ≡ c'' (mod 5)
    for d in CS:
        s, cpp, _ = S_C[d]
        tbl = {pow(3, a, 5): a % 4 for a in range(4)}   # 3^a mod 5 by a mod 4
        chk(tbl[cpp % 5] == {2: 0, 4: 1, 6: 0, 8: 0}[d], f"C11 a-exc residue d={d}")
    # b-exc: 9*7^b ≡ c'' (mod 5)
    tbl7 = {pow(9 * 7**b, 1, 5): b % 4 for b in range(4)}
    for d in CS:
        s, cpp, _ = S_C[d]
        want = {2: 2, 4: 1, 6: 2, 8: 2}[d]
        chk(tbl7[cpp % 5] == want, f"C11 b-exc residue d={d}")
    print("C11 ok" if ok else "C11 FAIL")
    # C12 structural sweep
    for d, c in CS.items():
        lam, mu = lam_mu(d)
        ell, r = ELL[d], R[d]
        v = 0
        for L in range(2, LMAX + 1):
            N = 10**L + c
            a = vp(N, 3); b = vp(N, 7)
            aexc = a >= 3 and L == lam.get(a)
            bexc = b >= 2 and L == mu.get(b)
            if 3**a > 9 * L and not aexc: v += 1
            if 7**b > 7 * L and not bexc: v += 1
            if not aexc and not bexc and 3**a * 7**b > 63 * L * L: v += 1
            if aexc and not (b == 0 and L % 3 == ell): v += 1
            if bexc and not (a == 2 and L % 6 == r): v += 1
            if aexc and bexc: v += 1
        print(f"C12 delta={d}: violations {v}")
        chk(v == 0, f"C12 d={d}")
    print("ALL CLOSING-ARGUMENT CERTIFICATE CHECKS PASSED" if ok else "FAILURES FOUND")

if __name__ == "__main__":
    main()
