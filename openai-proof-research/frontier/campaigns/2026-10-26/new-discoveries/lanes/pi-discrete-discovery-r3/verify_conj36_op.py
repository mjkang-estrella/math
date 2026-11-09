"""Exact N(n,k) = <chi_{J_{k,n}}, chi_n> via the adjoint differential-operator form:

  N(n,k) = ( prod_{(i,j) in J} (d_i - d_j) chi_n )(0),

chi_n = prod_{i<j}(x_i - x_j) = sum_{sigma} sgn(sigma) x^{alpha_sigma},
alpha_sigma(i) = sigma(i)-1.

DP: apply factors one at a time to the exponent-vector dict; prune entries that
cannot reach exponent 0 (a_v > number of remaining factors containing v, or a_v<0).
"""
import sys
from fractions import Fraction
from math import comb
from itertools import permutations

def pattern_J(n, k):
    J = []
    for i in range(1, n + 1):
        for j in range(i + 2, n + 1):
            J.append((i, j))
    for j in range(1, k + 1):
        J.append((n, j))
    for i in range(k + 1, n):
        J.append((i, 1))
    assert len(set(J)) == len(J)
    assert len(J) == comb(n, 2)
    return J

def N_op(n, k, verbose=False):
    J = pattern_J(n, k)
    # initial dict: monomials of chi_n
    poly = {}
    for perm in permutations(range(1, n + 1)):
        s = 1
        seen = [False] * (n + 1)
        for v in range(1, n + 1):
            if not seen[v]:
                l = 0; w = v
                while not seen[w]:
                    seen[w] = True; w = perm[w - 1]; l += 1
                if l % 2 == 0: s = -s
        poly[tuple(p - 1 for p in perm)] = Fraction(s)
    # order factors: process those containing the largest-index variable first,
    # so pruning (a_v <= remaining count) is effective.
    remaining = []
    for idx, f in enumerate(J):
        remaining.append(sum(1 for g in J[idx:] if g == f or set(g) & {f[0], f[1]}))
    # simpler: process factors in given order; prune with count of factors not yet applied containing v
    order = sorted(range(len(J)), key=lambda t: (max(J[t][0], J[t][1]), ), reverse=True)
    for step, t in enumerate(order):
        i, j = J[t]
        rem = {}
        # count remaining factors (after this one) containing each variable
        cnt = [0] * (n + 1)
        for t2 in order[step + 1:]:
            for v in J[t2]:
                cnt[v] += 1
        di, dj = poly, None
        new = {}
        for mono, c in di.items():
            if mono[i - 1] > 0:
                m2 = list(mono); m2[i - 1] -= 1
                if all(m2[v - 1] <= cnt[v] for v in range(1, n + 1)) and all(x >= 0 for x in m2):
                    t2_ = tuple(m2)
                    new[t2_] = new.get(t2_, 0) + c
            if mono[j - 1] > 0:
                m2 = list(mono); m2[j - 1] -= 1
                if all(m2[v - 1] <= cnt[v] for v in range(1, n + 1)) and all(x >= 0 for x in m2):
                    t2_ = tuple(m2)
                    new[t2_] = new.get(t2_, 0) - c
        poly = {m: c for m, c in new.items() if c != 0}
        if verbose: print(f"  factor {t+1}/{len(J)} ({i},{j}): dict size {len(poly)}", flush=True)
    return poly.get((0,) * n, Fraction(0))

def conjecture(n, k):
    return (-1) ** (n - 1) * comb(n, k) * comb(n - 2, k - 1)

if __name__ == "__main__":
    ok = True
    for n in range(2, int(sys.argv[1]) + 1):
        for k in range(1, n):
            v = N_op(n, k)
            c = conjecture(n, k)
            match = (v == c)
            ok &= match
            if not match or n >= 9:
                print(f"n={n} k={k}: N={v} conjecture={c} {'OK' if match else 'MISMATCH'}", flush=True)
    print("ALL MATCH" if ok else "MISMATCH FOUND")
