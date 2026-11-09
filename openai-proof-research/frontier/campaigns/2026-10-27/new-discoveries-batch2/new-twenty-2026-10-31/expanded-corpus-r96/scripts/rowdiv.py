"""382492: e-positivity of rowDiv_k(e_mu), mu |- kn (arXiv:2604.25440, Eq. (3) and the Conjecture in Sec. 4).

rowDiv_k(m_lambda) = m_{lambda/k} if every part of lambda is divisible by k, else 0.
[m_lambda] e_mu = M(mu, lambda) = number of 0-1 matrices with row sums mu and column sums lambda.
Hence rowDiv_k(e_mu) = sum_{nu |- n} M(mu, k nu) m_nu; we expand this in the e-basis using
e_lambda = sum_nu M(lambda, nu) m_nu (lambda, nu |- n), exact rational arithmetic.
Usage: rowdiv.py k nmax
"""
import sys, json, resource
from functools import lru_cache
from fractions import Fraction
from math import comb
resource.setrlimit(resource.RLIMIT_CPU, (115, 115))

def partitions(n, maxp=None):
    if maxp is None: maxp = n
    if n == 0:
        yield (); return
    for p in range(min(n, maxp), 0, -1):
        for rest in partitions(n - p, p):
            yield (p,) + rest

@lru_cache(maxsize=None)
def M(rows, cols):
    """# 0-1 matrices, row sums `rows` (tuple), column sums multiset `cols` (sorted tuple)."""
    if not rows:
        return 1 if all(c == 0 for c in cols) else 0
    r, rest = rows[0], rows[1:]
    # group columns by remaining value
    vals = {}
    for c in cols:
        if c > 0: vals[c] = vals.get(c, 0) + 1
    zeros = len(cols) - sum(vals.values())
    items = sorted(vals.items())
    total = 0
    def rec(i, need, newcols, mult):
        nonlocal total
        if i == len(items):
            if need == 0:
                total += mult * M(rest, tuple(sorted(newcols + [0] * zeros)))
            return
        v, cnt = items[i]
        for t in range(0, min(cnt, need) + 1):
            rec(i + 1, need - t, newcols + [v - 1] * t + [v] * (cnt - t), mult * comb(cnt, t))
    if sum(1 for c in cols if c > 0) < r:
        return 0
    rec(0, r, [], 1)
    return total

def solve_e(n, mvec):
    """mvec: dict nu -> coefficient of m_nu. Return dict lambda -> e-coefficient."""
    P = list(partitions(n))
    # e_lambda = sum_nu M(lambda,nu) m_nu ; M(lambda,nu) nonzero only if nu <= lambda' (dominance),
    # leading term m_{lambda'} with coefficient 1. Solve by peeling the dominance-largest m-term.
    rem = {nu: Fraction(c) for nu, c in mvec.items() if c}
    out = {}
    conj = lambda lam: tuple(sum(1 for x in lam if x > i) for i in range(lam[0])) if lam else ()
    order = P  # reverse lexicographic order refines dominance (largest first)
    for nu in order:
        c = rem.get(nu, 0)
        if c == 0: continue
        lam = conj(nu)  # e_lam has leading monomial m_nu
        out[lam] = c
        for nu2 in P:
            v = M(lam, tuple(sorted(nu2)))
            if v:
                rem[nu2] = rem.get(nu2, 0) - c * v
    assert all(v == 0 for v in rem.values())
    return out

def main(k, nmax):
    res = []
    for n in range(1, nmax + 1):
        Pn = list(partitions(n))
        neg = []; nonint = []; count = 0
        for mu in partitions(k * n):
            mvec = {nu: M(mu, tuple(sorted(k * x for x in nu))) for nu in Pn}
            e = solve_e(n, mvec)
            count += 1
            bad = {str(l): str(c) for l, c in e.items() if c < 0}
            if bad: neg.append({'mu': mu, 'neg': bad})
            if any(c.denominator != 1 for c in e.values()): nonint.append(mu)
        rec = {'k': k, 'n': n, 'mu_checked': count, 'negative': neg[:20], 'n_negative': len(neg), 'nonintegral': nonint[:20]}
        print(json.dumps(rec), flush=True)
        res.append(rec)

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]))
