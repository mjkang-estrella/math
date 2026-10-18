#!/usr/bin/env python3
"""MIT. Reviewer diagnostics for the uniform T205M lemmas at finitely many orders.

These finite tests probe the case analysis; they do not prove the universal
statements. Imports only the reviewer's own independent.py.
"""
import json, sys, importlib.util
from math import comb
from collections import Counter
from pathlib import Path
from functools import lru_cache

sp = importlib.util.spec_from_file_location('ind', Path(__file__).with_name('independent.py'))
I = importlib.util.module_from_spec(sp); sp.loader.exec_module(I)
plist, conj, kostka, E = I.plist, I.conj, I.kostka, I.E


# ---------------- Kirillov-Reshetikhin rigged configurations ----------------
def Qn(p, n):
    return sum(min(n, x) for x in p)


def kr_weight(alpha, mu, nus):
    """Weight prod binom(P+Q,Q) of configuration nus=[nu^(1),...,nu^(l-1)], or None if inadmissible.
    Shape alpha, content mu; Kirillov (1.6) with nu^(0)=mu; vacancies required at all n."""
    l = len(alpha)
    seq = [tuple(mu)] + [tuple(x) for x in nus] + [()]
    assert len(seq) == l + 1
    for k in range(1, l):
        if sum(seq[k]) != sum(alpha[k:]):
            return None
    top = max([1] + [x for p in seq for x in p]) + 2
    w = 1
    for k in range(1, l):
        mult = Counter(seq[k])
        for n in range(1, top + 1):
            P = Qn(seq[k - 1], n) - 2 * Qn(seq[k], n) + Qn(seq[k + 1], n)
            if P < 0:
                return None
            q = mult.get(n, 0)
            w *= comb(P + q, q)
    return w


def kr_total(alpha, mu):
    l = len(alpha)
    sizes = [sum(alpha[k:]) for k in range(1, l)]
    total = 0
    def rec(k, acc):
        nonlocal total
        if k == l - 1:
            w = kr_weight(alpha, mu, acc)
            if w:
                total += w
            return
        for p in plist(sizes[k]):
            rec(k + 1, acc + [p])
    rec(0, [])
    return total


def kr_formula_check(maxn):
    c = 0
    for n in range(1, maxn + 1):
        for a in plist(n):
            for mu in plist(n):
                assert kr_total(a, mu) == kostka(a, mu), (a, mu)
                c += 1
    return c


# ---------------- low-capacity Kostka lemma, exact and configuration-wise ----------------
def from_conj_cols(q):
    """partition whose conjugate is q (q nonincreasing, zeros allowed)."""
    q = [x for x in q if x > 0]
    return conj(tuple(q)) if q else ()


def maximal(alpha):
    return [tuple(alpha[k:]) for k in range(1, len(alpha))]


def perturbed(alpha, L, u, v):
    """move one cell of nu^(1) conjugate from column v to column u (1-based)."""
    q = [max(x - 1, 0) for x in L] + [0]
    q[u - 1] += 1; q[v - 1] -= 1
    if any(q[i] < q[i + 1] for i in range(len(q) - 1)) or q[v - 1] < 0:
        return None
    nus = maximal(alpha)
    nus[0] = from_conj_cols(q)
    return nus


def lowcap_check(d):
    N = d * (d + 1) // 2; rho = tuple(range(d, 0, -1))
    exc = {(1,) * N, (2,) + (1,) * (N - 2), (d - 1,) + (1,) * (N - d + 1), (d - 1, d - 1) + (1,) * (N - 2 * d + 2)}
    stats = Counter(); excvals = {}
    for L in plist(N):
        if L[0] > d - 1 or sum(L[:4]) > 2 * d:
            continue
        alpha = conj(L); K = kostka(alpha, rho)
        M = kr_weight(alpha, rho, maximal(alpha))
        assert M is not None and M <= K
        # explicit product formula (2.2)
        Lp = list(L) + [0]
        t = sum(1 for x in L if x >= 2); s = sum(1 for x in L if x == 1)
        D = lambda j: sum(rho[i] if i < d else 0 for i in range(j)) - sum(Lp[i] if i < len(L) else 0 for i in range(j))
        prod = 1
        for j in range(1, t + 1):
            dr = Lp[j - 1] - Lp[j]
            prod *= comb(D(j) + dr, dr)
        assert prod == M, (L, prod, M)
        if L in exc:
            excvals[str(L[:3])] = {'K': K, 'M': M}
            assert K >= (1 if L == (1,) * N else d - 1)
            stats['exception'] += 1
            continue
        assert K >= d, L
        w = L[0]
        # replay the case actually used by the proof
        if w == 2 and t > d and s <= d - 2:
            W = kr_weight(alpha, rho, [(t - 2, 2)] + [()] * (len(alpha) - 2))
            assert W is not None and W == (2 * d - 8) * (s + 1) and W >= d, (L, W)
            stats['width2-(t-2,2)'] += 1
        elif 3 <= w <= d - 2 and t >= 5:
            nus = perturbed(alpha, L, 1, t); W = kr_weight(alpha, rho, nus)
            assert W is not None
            bound = (d - w - 1) * (d - 2) if t <= d else (d - w - 1) * (w - 1)
            assert W >= bound, (L, W, bound)
            if w <= d - 3:
                assert W >= d
            else:
                assert M >= 3 and M + W >= d
            stats['perturb(1,t)'] += 1
        elif w == d - 1 and t >= 3 and (d - L[1]) >= d / 2:
            nus = perturbed(alpha, L, 2, t); W = kr_weight(alpha, rho, nus)
            a = d - L[1]
            assert W is not None and W >= (a - 1) ** 2 >= d, (L, W)
            stats['perturb(2,t)'] += 1
        else:
            assert M >= d, (L, M)
            stats['maximal'] += 1
    return dict(stats), excvals


# ---------------- uniform step case replay at order m ----------------
def interlace_preds(lam, k):
    out = []
    def rec(i, left, cur):
        if i == len(lam):
            if left == 0:
                out.append(tuple(x for x in cur if x))
            return
        lo = lam[i + 1] if i + 1 < len(lam) else 0
        for x in range(lo, lam[i] + 1):
            if lam[i] - x <= left:
                rec(i + 1, left - (lam[i] - x), cur + [x])
    rec(0, k, []); return out


def four_preds(lam, n):
    out = []
    def rec(i, left, cur):
        if i == len(lam):
            if left == 0:
                out.append(tuple(x for x in cur if x))
            return
        lo = lam[i + 4] if i + 4 < len(lam) else 0
        hi = min(lam[i], cur[-1] if cur else lam[0], left)
        for v in range(lo, hi + 1):
            rec(i + 1, left - v, cur + [v])
    rec(0, n, []); return out


def step_replay(m, use_kostka=True):
    n = m * (m + 1) // 2; h = m - 2; nh = h * (h + 1) // 2; rho = tuple(range(m, 0, -1))
    stats = Counter()
    for lam in plist(n):
        if lam in E(m):
            continue
        if lam[0] > m:
            rect = all(x == lam[0] for x in lam)
            if not rect:
                P = interlace_preds(lam, m)
                assert len(P) >= 2 and any(nu not in E(m - 1) for nu in P), lam
                stats['wide'] += 1
            else:
                a, b = lam[0], len(lam)
                nu1 = (a,) * (b - 2) + (a - m + 2, a - m - 1); nu2 = (a,) * (b - 2) + (a - m + 1, a - m)
                nu1 = tuple(x for x in nu1 if x); nu2 = tuple(x for x in nu2 if x)
                for nu, eta in ((nu1, (m + 1, m - 2)), (nu2, (m, m - 1))):
                    assert nu not in E(h) and I.lr_count_le4(lam, nu, by_content=True)[eta] == 1
                stats['rectangle'] += 1
            continue
        C = sum(lam[:4])
        if C >= 2 * m + 1:
            F = four_preds(lam, nh)
            assert sum(nu not in E(h) for nu in F) >= 2, lam
            stats['high'] += 1
            continue
        crit = (m, m - 2) + (1,) * (n - 2 * m + 2)
        if lam == crit:
            nu = (2,) + (1,) * (nh - 2)
            cont = I.lr_count_le4(lam, nu, by_content=True)
            assert cont[(m, m - 3, 1, 1)] >= 1 and cont[(m - 1, m - 2, 1, 1)] >= 1
            stats['critical'] += 1
            continue
        if use_kostka:
            assert kostka(conj(lam), rho) >= m - 1, lam
        stats['low-kostka'] += 1
    return dict(stats)


def highcap_check(m):
    n = m * (m + 1) // 2; h = m - 2; nh = h * (h + 1) // 2; c = 0; mn = None
    for lam in plist(n):
        if lam[0] > m or sum(lam[:4]) < 2 * m + 1:
            continue
        good = sum(nu not in E(h) for nu in four_preds(lam, nh))
        assert good >= 2, lam
        mn = good if mn is None else min(mn, good); c += 1
    return {'partitions': c, 'min_good_predecessors': mn}


def main():
    out = {}
    out['kr_formula_vs_kostka_pairs_n_le_7'] = kr_formula_check(7)
    print('kr ok', file=sys.stderr)
    for d in (8, 9, 10):
        out['lowcap_d%d' % d] = lowcap_check(d); print('lowcap', d, out['lowcap_d%d' % d][0], file=sys.stderr)
    for m in (7, 8, 9, 10):
        out['highcap_m%d' % m] = highcap_check(m); print('high', m, out['highcap_m%d' % m], file=sys.stderr)
    out['step_replay_m9'] = step_replay(9); print('step9', out['step_replay_m9'], file=sys.stderr)
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
