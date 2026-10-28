#!/usr/bin/env python3
"""Shifted Hankel determinants + the reduction to top-left blocks of B^r.

Theory to verify:
  Let B = K*D, K = I+S+S^T (path-graph adjacency incl. loops), D = diag(q^h).
  Claim R: det[M_{i+j+r}]_{i,j=0}^{n-1} = q^{n(n-1)(2n-1)/6} * det[(B^r)_{[0,n)x[0,n)}].
"""
from compute import M, padd, pmul, pstr, pzero, poly_divexact, hankel_det

def bmat_power_block(r, n):
    """(B^r) restricted to rows/cols [0,n): B_{j,i} = q^i for j in {i-1,i,i+1}.
    Walks from h'<n to h<n of length r stay within height <= n-1+r, so build
    the full matrix on [0, n-1+r] and take the n x n block."""
    N = n - 1 + r + 1  # heights 0..n-1+r
    B = {}
    for i in range(N):
        for j in (i - 1, i, i + 1):
            if 0 <= j < N:
                B[(j, i)] = {i: 1}
    # iterate
    P = {(h, h): {0: 1} for h in range(N)}
    for _ in range(r):
        Q = {}
        for (a, c), pa in P.items():
            for b in (c - 1, c, c + 1):
                if 0 <= b < N:
                    key = (a, b)
                    t = padd(pa, {})  # placeholder
                    add = pmul(pa, B.get((c, b), {}))
                    if add:
                        Q[key] = padd(Q.get(key, {}), add)
        P = Q
    return [[P.get((h, h2), {}) for h2 in range(n)] for h in range(n)]

def det_poly(mat):
    n = len(mat)
    A = [row[:] for row in mat]
    prev = {0: 1}
    sign = 1
    for k in range(n - 1):
        if A[k][k] == {}:
            for i in range(k + 1, n):
                if A[i][k] != {}:
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return {}
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = padd(pmul(A[k][k], A[i][j]),
                           {e: -c for e, c in pmul(A[i][k], A[k][j]).items()})
                A[i][j] = num if k == 0 else poly_divexact(num, prev)
        prev = A[k][k]
    return {e: c * sign for e, c in A[n - 1][n - 1].items()}

def qshift(a, m):
    return {e + m: c for e, c in a.items()}

if __name__ == "__main__":
    print("=== Verify Claim R: Delta^r_n == q^{n(n-1)(2n-1)/6} * det[(B^r)_{n x n]} ===")
    ok = True
    for r in range(0, 8):
        for n in range(1, 6):
            lhs = hankel_det(r, n)
            Bb = det_poly(bmat_power_block(r, n))
            rhs = qshift(Bb, n * (n - 1) * (2 * n - 1) // 6)
            same = (lhs == rhs)
            if not same:
                ok = False
                print(f"MISMATCH r={r} n={n}: hankel={pstr(lhs)} vs qshift={pstr(rhs)}")
    print("Claim R verified" if ok else "Claim R FAILED")

    print()
    print("=== Shifted Hankel determinants Delta^{(r)}_n ===")
    for r in range(0, 9):
        for n in range(1, 7):
            d = hankel_det(r, n)
            pos = pzero(d)
            neg = any(c < 0 for c in d.values())
            print(f"r={r} n={n}: {'POS' if pos else ('NEG' if neg else 'ZERO')}  {pstr(d) if len(pstr(d))<120 else pstr(d)[:120]+'...'}")
        print()
