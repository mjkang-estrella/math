#!/usr/bin/env python3
"""MIT. Independent reviewer recomputation for T205M finite bases and diagnostics.

Written without importing the author packet. Algorithms deliberately differ:
characters come from permutation-module characters and triangular Kostka
inversion; LR sums are counted by explicit lattice-word tableaux; strip
predecessors are found by containment and conjugate column tests.
Finite checks only; the uniform theorem is checked in prose.
"""
import json, sys, hashlib
from fractions import Fraction
from functools import lru_cache
from math import factorial, comb
from collections import Counter


def partitions(n, top=None):
    top = n if top is None else top
    if n == 0:
        yield ()
        return
    for a in range(min(n, top), 0, -1):
        for rest in partitions(n - a, a):
            yield (a,) + rest


@lru_cache(None)
def plist(n):
    return tuple(partitions(n))


def conj(lam):
    return tuple(sum(1 for x in lam if x > j) for j in range(lam[0])) if lam else ()


def contained(nu, lam):
    return len(nu) <= len(lam) and all(a <= lam[i] for i, a in enumerate(nu))


def colgaps(lam, nu):
    lc, nc = conj(lam), conj(nu)
    return [lc[j] - (nc[j] if j < len(nc) else 0) for j in range(len(lc))]


# ---------- Kostka numbers: add letters 1,2,... as horizontal strips ----------
@lru_cache(None)
def kostka(shape, content):
    """Number of SSYT of `shape` with letter i used content[i] times."""
    @lru_cache(None)
    def grow(cur, i):
        if i == len(content):
            return int(cur == shape)
        total = 0
        k = content[i]
        # add a horizontal strip of size k to cur staying inside shape
        rows = len(shape)
        def rec(r, left, new):
            nonlocal total
            if r == rows:
                if left == 0:
                    total_list.append(tuple(x for x in new if x))
                return
            old = cur[r] if r < len(cur) else 0
            prev_old = (cur[r - 1] if r - 1 < len(cur) else 0) if r > 0 else None
            hi = shape[r] if r == 0 else min(shape[r], prev_old)
            for x in range(old, hi + 1):
                if x - old <= left:
                    rec(r + 1, left - (x - old), new + [x])
        total_list = []
        rec(0, k, [])
        return sum(grow(nx, i + 1) for nx in total_list)
    return grow((), 0)


# ---------- characters via permutation modules and Kostka inversion ----------
def perm_char(mu, cyc):
    """Character of M^mu at cycle type cyc: number of ways to place cycles in blocks."""
    @lru_cache(None)
    def place(i, caps):
        if i == len(cyc):
            return int(all(c == 0 for c in caps))
        s = 0
        for b, c in enumerate(caps):
            if c >= cyc[i]:
                s += place(i + 1, caps[:b] + (c - cyc[i],) + caps[b + 1:])
        return s
    return place(0, tuple(mu))


def dominates(a, b):
    sa = sb = 0
    for i in range(max(len(a), len(b))):
        sa += a[i] if i < len(a) else 0
        sb += b[i] if i < len(b) else 0
        if sa < sb:
            return False
    return True


@lru_cache(None)
def char_table(n):
    ps = plist(n)
    # M^mu = sum_lambda K_{lambda,mu} S^lambda, lambda >= mu; solve from the top of dominance
    order = sorted(ps, key=lambda p: [-x for x in p])  # lexicographically largest first
    chars = {}
    for mu in order:
        row = {c: perm_char(mu, c) for c in ps}
        for lam in chars:
            K = kostka(lam, mu)
            if K:
                for c in ps:
                    row[c] -= K * chars[lam][c]
        chars[mu] = row  # K_{mu,mu}=1
    return chars


def zee(c):
    v = 1
    for j, a in Counter(c).items():
        v *= j ** a * factorial(a)
    return v


def kron_square_min(m):
    rho = tuple(range(m, 0, -1)); n = sum(rho); ch = char_table(n); ps = plist(n)
    # sanity: orthogonality and dimension
    for a in ps:
        for b in ps:
            ip = sum(Fraction(ch[a][c] * ch[b][c], zee(c)) for c in ps)
            assert ip == (a == b)
    g = {}
    for lam in ps:
        v = sum(Fraction(ch[rho][c] ** 2 * ch[lam][c], zee(c)) for c in ps)
        assert v.denominator == 1 and v >= 0
        g[lam] = int(v)
    one = (1,) * n
    dimr = ch[rho][one]
    assert sum(g[l] * ch[l][one] for l in ps) == dimr ** 2
    rest = {l: v for l, v in g.items() if l not in [(n,), (1,) * n]}
    return g, min(rest.values()), sorted(l for l, v in rest.items() if v == min(rest.values()))


# ---------- LR counts: tableaux of shape lam/nu, entries <= 4, lattice reverse reading word ----------
def lr_count_le4(lam, nu, maxlen=4, by_content=False):
    cells = []
    for i, a in enumerate(lam):
        b = nu[i] if i < len(nu) else 0
        for j in range(a - 1, b - 1, -1):  # reverse reading: rows top to bottom, right to left
            cells.append((i, j))
    fill = {}
    out = Counter()

    def rec(k, cnt):
        if k == len(cells):
            out[tuple(x for x in cnt if x)] += 1
            return
        i, j = cells[k]
        lo = 1
        if (i - 1, j) in fill:
            lo = fill[(i - 1, j)] + 1
        hi = maxlen
        if (i, j + 1) in fill:
            hi = min(hi, fill[(i, j + 1)])
        for v in range(lo, hi + 1):
            if v > 1 and cnt[v - 2] <= cnt[v - 1]:
                continue  # lattice condition: #v so far must stay <= #(v-1)
            fill[(i, j)] = v
            cnt[v - 1] += 1
            rec(k + 1, cnt)
            cnt[v - 1] -= 1
            del fill[(i, j)]
    # cells above in the same column with nu boundary are not filled: column strictness only within skew
    rec(0, [0] * maxlen)
    return out if by_content else sum(out.values())


def E(h):
    n = h * (h + 1) // 2
    return {(n,), (1,) * n, (h,) + (1,) * (n - h), (h, 2) + (1,) * (n - h - 2)}


def subparts_inside(lam, size):
    return [nu for nu in plist(size) if contained(nu, lam)]


def hpreds(lam, k):
    n = sum(lam) - k
    return [nu for nu in subparts_inside(lam, n) if all(g <= 1 for g in colgaps(lam, nu))]


def fourpreds(lam, size):
    return [nu for nu in subparts_inside(lam, size) if all(g <= 4 for g in colgaps(lam, nu))]


def cyclic_R(top):
    R = {1: {(1,): 1}}
    for m in range(2, top + 1):
        n = m * (m + 1) // 2; rho = tuple(range(m, 0, -1)); Rm = {}
        for lam in plist(n):
            one = sum(R[m - 1][nu] for nu in hpreds(lam, m))
            two = 0
            if m >= 3:
                for nu in subparts_inside(lam, n - (2 * m - 1)):
                    if all(g <= 4 for g in colgaps(lam, nu)):
                        two += R[m - 2][nu] * lr_count_le4(lam, nu)
            K = kostka(conj(lam), rho)
            Rm[lam] = max(1, K, one, two)
        R[m] = Rm
        print('R', m, len(Rm), file=sys.stderr)
    return R


def boundary(m):
    n = m * (m + 1) // 2; h = m - 2; nh = h * (h + 1) // 2; rho = tuple(range(m, 0, -1))
    stats = Counter(); critical = []
    for lam in plist(n):
        if lam in E(m):
            continue
        preds = hpreds(lam, m)
        good = sum(nu not in E(m - 1) for nu in preds)
        if (m - 2) * good + (len(preds) - good) >= m - 1:
            stats['one'] += 1; continue
        if kostka(conj(lam), rho) >= m - 1:
            stats['K'] += 1; continue
        total = 0
        for nu in fourpreds(lam, nh):
            w = (m - 3) if nu not in E(h) else 1
            total += w * lr_count_le4(lam, nu)
        assert total >= m - 1, lam
        stats['two-band-exact-LR'] += 1
        critical.append({'lambda': list(lam), 'two_band_weighted_LR': total})
    return dict(stats), critical


def lr_crosscheck():
    """LR counts versus character induction of S^nu x S^eta for small sizes."""
    checks = 0
    for a in range(1, 5):
        for b in range(1, 6):
            n = a + b; ch = char_table(n); cha = char_table(a); chb = char_table(b)
            for nu in plist(a):
                for eta in plist(b):
                    if len(eta) > 4:
                        continue
                    for lam in plist(n):
                        # <Ind chi^nu x chi^eta, chi^lam> via restriction to S_a x S_b
                        v = Fraction(0)
                        for c1 in plist(a):
                            for c2 in plist(b):
                                c = tuple(sorted(c1 + c2, reverse=True))
                                v += Fraction(cha[nu][c1] * chb[eta][c2] * ch[lam][c], zee(c1) * zee(c2))
                        lr = lr_count_le4(lam, nu, by_content=True)[eta] if contained(nu, lam) else 0
                        assert v == lr, (lam, nu, eta, v, lr)
                        checks += 1
    return checks


def main():
    out = {}
    out['lr_vs_induction_checks'] = lr_crosscheck()
    small = {}
    for m in (2, 3, 4):
        g, mn, arg = kron_square_min(m)
        assert mn == m - 1
        small[m] = {'min': mn, 'minimizers': [list(x) for x in arg]}
    out['small_squares'] = small
    R = cyclic_R(6)
    for h in (5, 6):
        bad = [l for l, v in R[h].items() if l not in E(h) and v < h - 1]
        assert not bad
        out['R%d_nonexceptional' % h] = sum(1 for l in R[h] if l not in E(h))
        out['R%d_min_nonexceptional' % h] = min(v for l, v in R[h].items() if l not in E(h))
        out['R%d_on_exceptions' % h] = {str(l if len(l) < 4 else l[:3] + ('...',)): R[h][l] for l in E(h)}
    for m in (7, 8):
        st, crit = boundary(m)
        out['boundary_%d' % m] = {'stats': st, 'nontrivial': crit}
        print('boundary', m, st, file=sys.stderr)
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
