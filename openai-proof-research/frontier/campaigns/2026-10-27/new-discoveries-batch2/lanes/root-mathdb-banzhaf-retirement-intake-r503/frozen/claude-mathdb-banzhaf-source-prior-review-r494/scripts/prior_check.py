"""Exact check of prior one-big-player witnesses against arXiv:1801.08029 Conjecture 3.8.

Game: one player of integer weight a, m players of weight 1, integer quota T (win iff weight >= T).
Swing counts (own derivation, s = number of unit players in the coalition):
  big:  critical iff a + s >= T and s < T, i.e. max(0, T-a) <= s <= min(m, T-1)  -> sum C(m, s)
  unit: critical with big iff s = T-a (1 <= T-a <= m)  -> C(m-1, T-a-1)
        critical without big iff s = T (1 <= T <= m)   -> C(m-1, T-1)
Closed form is cross-checked against brute force (indep_check.game) for small m.
Bound tested: index <= 2*max(w)/N, N = a + m; for a >= 1, max(w) = a.
"""
from fractions import Fraction as Fr
from math import comb
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from indep_check import game  # noqa: E402


def closed(a, m, T):
    big = sum(comb(m, s) for s in range(max(0, T - a), min(m, T - 1) + 1))
    unit = 0
    if 1 <= T - a <= m:
        unit += comb(m - 1, T - a - 1)
    if 1 <= T <= m:
        unit += comb(m - 1, T - 1)
    return big, unit


def check(label, a, m, T):
    N = a + m
    big, unit = closed(a, m, T)
    tot = big + m * unit
    norm = Fr(big, tot)
    absb = Fr(big, 2 ** m)  # 2^(n-1) with n = m+1 players
    bound = Fr(2 * max(a, 1), N)
    print(f"== {label}: a={a} m={m} T={T} N={N} T/N={float(Fr(T, N)):.6f} 2w/N={bound} (~{float(bound):.6f})")
    print(f"   big swings={big if big < 10**30 else '<' + str(big.bit_length()) + '-bit int>'} unit swings each={unit if unit < 10**30 else '<' + str(unit.bit_length()) + '-bit int>'}")
    print(f"   normalized big ~ {float(norm):.9f}  > bound: {norm > bound}   ratio norm/(w/N) ~ {float(norm / Fr(a, N)):.6f}")
    print(f"   absolute   big ~ {float(absb):.9f}  > bound: {absb > bound}")
    return norm > bound, absb > bound


def main():
    # brute-force cross-check of the closed form
    n_cases = 0
    for m in range(0, 9):
        for a in range(1, 10):
            for T in range(1, a + m + 1):
                _, gam = game([a] + [1] * m, T)
                big, unit = closed(a, m, T)
                assert gam[0] == big and all(g == unit for g in gam[1:]), (a, m, T)
                n_cases += 1
    print("closed form == brute force on", n_cases, "games (m<=8, a<=9, all T)")
    # brief's witness B is the case a=7, m=8, T=8
    assert check("brief B (apex k=7)", 7, 8, 8) == (True, True)
    # Gafni-Lavi-Tennenholtz (arXiv:2108.09216v1 / JAIR 72) Appendix C family: A={2k}, m=k^1.5, T=(2k+k^1.5)/2
    for nk in (1, 2, 3, 4, 10, 20):
        k = (2 * nk) ** 2
        m = round(k ** 1.5)
        assert m ** 2 == k ** 3
        a = 2 * k
        T = (a + m) // 2
        assert 2 * T == a + m
        res = check(f"GLT Appendix C k={k}", a, m, T)
        if k >= 16:
            assert res[0], k
    # Example 4.1 (k=1600): A={3200}, m=64000, T=33600
    assert check("GLT Example 4.1 k=1600", 3200, 64000, 33600) == (True, True)


if __name__ == "__main__":
    main()
