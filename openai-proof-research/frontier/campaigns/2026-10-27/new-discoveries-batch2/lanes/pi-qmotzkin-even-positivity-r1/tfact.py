#!/usr/bin/env python3
"""Verify det[(B^{2k})_{n x n}] = q^{binom n 2} * sum_M det[T_{[0,n),M}]^2 q^{sum M}
with T = B^k D^{-1}, and test whether these T-minors are in Z>=0[q]."""
from compute import padd, pmul, pstr, pzero, poly_divexact
from reduce import bmat_power_block, det_poly
from itertools import combinations

def bpower_entry(r, h, m, Hmax):
    """(B^r)_{h,m} = walks m->h of length r, weight q^{source heights}.
    Iterating (B^{s+1})_{a,b} = sum_c B_{a,c} (B^s)_{c,b} with B_{a,c} = q^c."""
    N = Hmax + 1
    P = {(a, c): ({0: 1} if a == c else {}) for a in range(N) for c in range(N)}
    for _ in range(r):
        Q = {}
        for (a, c), pa in P.items():
            if not pa:
                continue
            for b in (c - 1, c, c + 1):
                if 0 <= b < N:
                    # B_{c,b} = q^b (source = column b)
                    add = pmul(pa, {b: 1})
                    Q[(a, b)] = padd(Q.get((a, b), {}), add)
        P = Q
    return P.get((h, m), {})

def T_matrix(k, n, Hmax):
    """T = B^k D^{-1} entries T_{h,m} = (B^k)_{h,m} q^{-m}, rows h in [0,n), cols m in [0,Hmax]."""
    T = []
    for h in range(n):
        row = []
        for m in range(Hmax + 1):
            e = bpower_entry(k, h, m, Hmax)
            row.append({t - m: c for t, c in e.items()})
        T.append(row)
    return T

def minor_poly(mat, rows, cols):
    A = [[mat[r][c] for c in cols] for r in rows]
    return det_poly(A)

if __name__ == "__main__":
    print("=== Verify identity (B) and test T-minors ===")
    for k in (1, 2, 3):
        for n in range(1, 6):
            Hmax = n + 2 * k + 2
            T = T_matrix(k, n, Hmax)
            # sum over all n-subsets M of columns
            tot = {}
            npos = nneg = 0
            for M in combinations(range(Hmax + 1), n):
                d = minor_poly(T, range(n), M)
                if not d:
                    continue
                sq = pmul(d, d)
                tot = padd(tot, pmul({sum(M): 1}, sq))
                if pzero(d):
                    npos += 1
                else:
                    nneg += 1
            lhs = det_poly(bmat_power_block(2 * k, n))
            rhs = {e - n * (n - 1) // 2: c for e, c in tot.items()}  # multiply by q^{-binom n 2}? no:
            # identity: det[(B^{2k})] = q^{binom n 2} * sum; so sum should equal q^{-binom} * lhs
            expect = {e - n * (n - 1) // 2: c for e, c in lhs.items()}
            match = (tot == expect)
            print(f"k={k} n={n}: identity {'OK' if match else 'FAIL'}  T-minors: {npos} nonneg-coeff, {nneg} mixed/neg")
            if not match:
                print("  lhs:", pstr(lhs)[:200]); print("  sum:", pstr(tot)[:200])
            elif nneg:
                print("  sum:", pstr(tot)[:220])
