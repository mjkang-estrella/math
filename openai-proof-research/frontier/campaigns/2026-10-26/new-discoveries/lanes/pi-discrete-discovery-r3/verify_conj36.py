"""Exact verification of An-Djokovic Conjecture 3.6 (MathDB 381028).

N(n,k) = <chi_{J_{k,n}}, chi_n> = (-1)^{C(n,2)} sum_sigma sgn(sigma) [x^{alpha_sigma}] chi_J
where alpha_sigma(i) = sigma(i)-1, and chi_n = prod_{i<j}(x_i-x_j),
J_{k,n} = {(i,j): 1<=i, j>=i+2, j<=n} (=(0,1)+NE_{n-1})
        union {(n,j): 1<=j<=k}
        union {(i,1): k<i<n}.

Conjecture: N(n,k) = (-1)^{n-1} C(n,k) C(n-2,k-1).

DP over factors with pruning exponent_i <= n-1 (valid: only staircase monomials needed).
"""
import sys
from fractions import Fraction
from math import comb
from itertools import permutations

def pattern_J(n, k):
    J = []
    for i in range(1, n + 1):          # A = (0,1)+NE_{n-1}
        for j in range(i + 2, n + 1):
            J.append((i, j))
    for j in range(1, k + 1):          # B = {n} x Z_k
        J.append((n, j))
    for i in range(k + 1, n):          # C
        J.append((i, 1))
    assert len(set(J)) == len(J), "pattern not strict"
    assert len(J) == comb(n, 2), f"|J|={len(J)} != {comb(n,2)}"
    return J

def chi_J_coeffs(n, k):
    """dict: exponent tuple -> Fraction coefficient of chi_J, pruned to exp_i <= n-1."""
    J = pattern_J(n, k)
    poly = {(0,) * n: Fraction(1)}
    for (i, j) in J:
        # factor (x_i - x_j), 1-indexed
        a, b = i - 1, j - 1
        new = {}
        for mono, c in poly.items():
            # choose x_i
            if mono[a] + 1 <= n - 1:
                m2 = list(mono); m2[a] += 1
                t = tuple(m2)
                new[t] = new.get(t, 0) + c
            # choose -x_j
            if mono[b] + 1 <= n - 1:
                m2 = list(mono); m2[b] += 1
                t = tuple(m2)
                new[t] = new.get(t, 0) - c
        poly = {m: c for m, c in new.items() if c != 0}
    return poly

def staircase_map(n):
    """map exponent tuple (sigma(i)-1) -> sgn(sigma), for all sigma in S_n."""
    out = {}
    for perm in permutations(range(1, n + 1)):
        # compute sign
        s = 1
        seen = [False] * (n + 1)
        for v in range(1, n + 1):
            if not seen[v]:
                # cycle detection
                l = 0
                w = v
                while not seen[w]:
                    seen[w] = True
                    w = perm[w - 1]
                    l += 1
                if l % 2 == 0:
                    s = -s
        alpha = tuple(p - 1 for p in perm)
        out[alpha] = s
    return out

def N(n, k):
    poly = chi_J_coeffs(n, k)
    smap = staircase_map(n)
    mu = comb(n, 2)
    total = Fraction(0)
    for alpha, sg in smap.items():
        c = poly.get(alpha)
        if c:
            total += sg * c
    return (-1) ** mu * total

def conjecture(n, k):
    return (-1) ** (n - 1) * comb(n, k) * comb(n - 2, k - 1)

if __name__ == "__main__":
    ok = True
    for n in range(2, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 9):
        row = []
        for k in range(1, n):
            v = N(n, k)
            c = conjecture(n, k)
            match = (v == c)
            ok &= match
            row.append(f"k={k}:{v}{'=' if match else '!=' + str(c)}")
        print(f"n={n}: " + "  ".join(row), flush=True)
    print("ALL MATCH" if ok else "MISMATCH FOUND")
