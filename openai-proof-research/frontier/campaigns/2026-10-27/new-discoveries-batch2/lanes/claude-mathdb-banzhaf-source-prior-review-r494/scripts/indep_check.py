"""Independent exact check for MathDB 338290 (arXiv:1801.08029 Conjecture 3.8).

Written from the source definitions only (Section 1 / 2.1.1, no association matrix):
  C winning iff sum_{i in C} w_i >= q;  (i, C) critical iff i in C, C winning, C - {i} losing.
  gamma_i = #critical pairs; beta_i = gamma_i / 2^(m-1); beta~_i = gamma_i / sum_j gamma_j.
Bound under test: index_i <= 2 * max(w) / sum(w).
All arithmetic is exact (Fraction).  Bounded search results are evidence only, not proofs.
"""
from fractions import Fraction as Fr
from itertools import combinations_with_replacement
from math import comb
import sys


def game(w, q):
    m = len(w)
    wt = [0] * (1 << m)
    for s in range(1, 1 << m):
        low = (s & -s).bit_length() - 1
        wt[s] = wt[s & (s - 1)] + w[low]
    win = [x >= q for x in wt]
    gam = [0] * m
    for s in range(1 << m):
        if not win[s]:
            continue
        for i in range(m):
            if s >> i & 1 and not win[s & ~(1 << i)]:
                gam[i] += 1
    return win, gam


def indices(w, q):
    m = len(w)
    win, gam = game(w, q)
    tot = sum(gam)
    W = sum(win)
    L = (1 << m) - W
    absb = [Fr(g, 1 << (m - 1)) for g in gam]
    norm = [Fr(g, tot) if tot else None for g in gam]
    prevent = [Fr(g, W) if W else None for g in gam]   # Coleman power to prevent action
    initiate = [Fr(g, L) if L else None for g in gam]  # Coleman power to initiate action
    return dict(gamma=gam, total=tot, W=W, L=L, abs=absb, norm=norm,
                prevent=prevent, initiate=initiate)


def props(w, q):
    """proper: S, complement(S) not both winning; strong: not both losing."""
    m = len(w)
    win, _ = game(w, q)
    full = (1 << m) - 1
    proper = all(not (win[s] and win[full ^ s]) for s in range(1 << m))
    strong = all(win[s] or win[full ^ s] for s in range(1 << m))
    return proper, strong


def report(name, w, q):
    N = sum(w)
    bound = Fr(2 * max(w), N)
    r = indices(w, q)
    pr, st = props(w, q)
    print(f"== {name}: w={w} q={q} N={N} 2w/N={bound} q>N/2:{2*q>N} proper:{pr} strong:{st}")
    print(f"   gamma={r['gamma']} total_swings={r['total']} |W|={r['W']} |L|={r['L']}")
    for key in ("abs", "norm", "prevent", "initiate"):
        v = r[key]
        viol = [i for i, x in enumerate(v) if x is not None and x > bound]
        print(f"   {key:8s} player0={v[0]} max={max(x for x in v if x is not None)} violators={viol}")
    return r, bound


def main():
    # A: brief's absolute witness
    rA, bA = report("A", [3, 1, 1, 1, 1], 4)
    assert rA["gamma"][0] == 14 and rA["abs"][0] == Fr(7, 8) and bA == Fr(6, 7) and Fr(7, 8) > Fr(6, 7)
    assert 7 * 7 > 6 * 8
    # B: brief's normalized witness
    rB, bB = report("B", [7] + [1] * 8, 8)
    assert rB["gamma"] == [254] + [2] * 8 and rB["total"] == 270
    assert rB["norm"][0] == Fr(127, 135) and bB == Fr(14, 15)
    assert 127 * 15 == 1905 and 14 * 135 == 1890 and rB["norm"][0] > bB
    assert rB["abs"][0] == Fr(254, 256) > bB
    # Classical equal-weight simple majority (Penrose / Dubey-Shapley): absolute reading
    for m in range(1, 16):
        q = m // 2 + 1
        r = indices([1] * m, q)
        expect = Fr(comb(m - 1, q - 1), 1 << (m - 1))
        assert r["abs"][0] == expect
        assert all(x == Fr(1, m) for x in r["norm"])
        flag = expect > Fr(2, m)
        print(f"   equal m={m:2d} q={q:2d} abs={expect} 2/m={Fr(2, m)} abs-violates={flag} norm=1/m ok")
    report("equal-7", [1] * 7, 4)
    # Apex family (k; 1^(k+1)), q = k+1: enumeration vs closed form
    print("== apex family")
    first = None
    for k in range(1, 15):
        n = k + 1
        w = [k] + [1] * n
        q = k + 1
        r = indices(w, q)
        assert r["gamma"] == [2 ** n - 2] + [2] * n
        N = 2 * k + 1
        bound = Fr(2 * k, N)
        nv = r["norm"][0] > bound
        assert nv == (2 ** (k + 1) > 4 * k * k + 4 * k + 2)
        pr, st = props(w, q)
        assert pr and st
        if nv and first is None:
            first = k
        print(f"   k={k:2d} norm_apex={r['norm'][0]} bound={bound} norm-violates={nv} abs-violates={r['abs'][0] > bound}")
    print("   first normalized violation in apex family k =", first)
    # Closed-form threshold 2^(k+1) > 4k^2+4k+2 for all k>=7: holds at 7; if 2^(k+1) > 4k^2+4k+2
    # then 2^(k+2) > 8k^2+8k+4 >= 4(k+1)^2+4(k+1)+2 = 4k^2+12k+10 iff 4k^2 >= 4k+6, true for k>=2.
    assert 2 ** 8 > 4 * 49 + 28 + 2 and not (2 ** 7 > 4 * 36 + 24 + 2)
    # Bounded search (evidence only): normalized violations, m <= M, integer weights <= Wmax, all quotas.
    M, Wmax = int(sys.argv[1]), int(sys.argv[2])
    cnt = 0
    for m in range(1, M + 1):
        for w in combinations_with_replacement(range(1, Wmax + 1), m):
            w = list(w)
            N = sum(w)
            bound = Fr(2 * max(w), N)
            for q in range(1, N + 1):
                _, gam = game(w, q)
                tot = sum(gam)
                if tot and any(Fr(g, tot) > bound for g in gam):
                    cnt += 1
                    if cnt <= 5:
                        print("   bounded-search normalized violation", w, q)
    print(f"== bounded search m<={M}, weights<={Wmax}: normalized violations found = {cnt}")


if __name__ == "__main__":
    main()
