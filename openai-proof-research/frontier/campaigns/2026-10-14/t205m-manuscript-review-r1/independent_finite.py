#!/usr/bin/env python3
"""Reviewer-independent recomputation of the T205M finite starts.

Imports nothing from the author or manuscript packets.  Algorithms differ
from the author's beta-set / character-induction code:
  * characters: Murnaghan--Nakayama with rim hooks indexed by diagram cells
    of the given hook length (row-shift formula), not beta-set beads;
  * four-row LR sums sum_{len(eta)<=4} c^lam_{nu,eta}: skew Kostka numbers
    in four letters plus Weyl alternation over S_4, not character induction
    and not lattice-word tableaux;
  * Kostka numbers: largest-letter strip removal (classical), cross-checked
    against brute-force SSYT enumeration for n<=8.
The certificate is read only to compare entries after recomputation.
Exact integers/Fractions only.  SPDX-License-Identifier: MIT
"""
import itertools, json, multiprocessing, sys
from fractions import Fraction
from functools import lru_cache
from math import factorial
from collections import Counter
from pathlib import Path

CERT = (Path(__file__).resolve().parents[1] /
        't205m-manuscript-v1/public/code/finite-proof-certificate.json')


# ---------- partitions ----------
@lru_cache(None)
def partitions(n, cap=None):
    cap = n if cap is None else cap
    if n == 0:
        return ((),)
    out = []
    for first in range(min(n, cap), 0, -1):
        for rest in partitions(n - first, first):
            out.append((first,) + rest)
    return tuple(out)


def conj(lam):
    return tuple(sum(1 for x in lam if x > j) for j in range(lam[0])) if lam else ()


def N(m):
    return m * (m + 1) // 2


def stair(m):
    return tuple(range(m, 0, -1))


def exceptions(h):
    n = N(h)
    return {(n,), (1,) * n, (h,) + (1,) * (n - h), (h, 2) + (1,) * (n - h - 2)}


# ---------- characters via cell-indexed rim hooks ----------
@lru_cache(None)
def rim_hooks(lam, k):
    """All (new_shape, sign) obtained by removing a rim hook of size k.
    Cell (i,j) of hook length k determines the rim hook running from the end
    of row i to the bottom of column j.  Rows i..i2 become
    lam[r+1]-1 (r<i2) and j (r=i2), where i2 = last row of column j."""
    lt = conj(lam)
    res = []
    for i, row in enumerate(lam):
        for j in range(row):
            i2 = lt[j] - 1
            if (row - j) + (i2 - i) - 1 + 1 != k:
                continue
            new = list(lam)
            for r in range(i, i2):
                new[r] = lam[r + 1] - 1
            new[i2] = j
            new = tuple(x for x in new if x > 0)
            res.append((new, -1 if (i2 - i) % 2 else 1))
    return tuple(res)


@lru_cache(None)
def char(lam, mu):
    if not mu:
        return 1 if not lam else 0
    return sum(s * char(nu, mu[1:]) for nu, s in rim_hooks(lam, mu[0]))


def zee(mu):
    z = 1
    for part, c in Counter(mu).items():
        z *= part ** c * factorial(c)
    return z


def kronecker_square(m):
    n, rho = N(m), stair(m)
    cls = [(mu, char(rho, mu), zee(mu)) for mu in partitions(n)]
    assert sum(Fraction(c * c, z) for _, c, z in cls) == 1
    g = {}
    for lam in partitions(n):
        v = sum(Fraction(c * c * char(lam, mu), z) for mu, c, z in cls if c)
        assert v.denominator == 1 and v >= 0
        g[lam] = int(v)
    return g


# ---------- Kostka ----------
def strips_below(lam, k, floor=()):
    """Partitions kappa with floor subset kappa, lam/kappa a horizontal k-strip."""
    L = len(lam)
    fl = list(floor) + [0] * (L - len(floor))
    out = []

    def rec(i, left, cur):
        if i == L:
            if left == 0:
                out.append(tuple(x for x in cur if x))
            return
        lo = max(lam[i + 1] if i + 1 < L else 0, fl[i])
        for x in range(lam[i], lo - 1, -1):
            if lam[i] - x > left:
                break
            rec(i + 1, left - (lam[i] - x), cur + [x])
    rec(0, k, [])
    return out


@lru_cache(None)
def kostka(lam, mu):
    if not mu:
        return 1 if not lam else 0
    if sum(lam) != sum(mu) or len(lam) > len(mu):
        return 0
    return sum(kostka(k, mu[:-1]) for k in strips_below(lam, mu[-1]))


def kostka_brute(lam, mu):
    """Brute-force SSYT count, n<=8 only."""
    cells = [(i, j) for i, r in enumerate(lam) for j in range(r)]
    letters = [a + 1 for a, c in enumerate(mu) for _ in range(c)]
    cnt = 0
    for perm in set(itertools.permutations(letters)):
        T = dict(zip(cells, perm))
        if all((j == 0 or T[(i, j - 1)] <= T[(i, j)]) and
               (i == 0 or T[(i - 1, j)] < T[(i, j)]) for i, j in cells):
            cnt += 1
    return cnt


# ---------- four-row LR sums ----------
DELTA = (3, 2, 1, 0)
PERMS = [(p, (-1) ** sum(1 for a in range(4) for b in range(a + 1, 4) if p[a] > p[b]))
         for p in itertools.permutations(range(4))]


def contains(lam, nu):
    return len(nu) <= len(lam) and all(nu[i] <= lam[i] for i in range(len(nu)))


def skew_content_polynomial(lam, nu):
    """Map content (b1,b2,b3,b4) -> number of SSYT of shape lam/nu in letters 1..4,
    built letter by letter from horizontal strips nu = k0 < k1 < ... < k4 = lam."""
    L = len(lam)
    start = tuple(list(nu) + [0] * (L - len(nu)))
    states = {start: Counter({(): 1})}
    for _ in range(4):
        nxt = {}
        for kap, poly in states.items():
            def rec(i, cur):
                if i == L:
                    new = tuple(cur)
                    add = sum(new) - sum(kap)
                    tgt = nxt.setdefault(new, Counter())
                    for c, v in poly.items():
                        tgt[c + (add,)] += v
                    return
                hi = lam[i] if i == 0 else min(lam[i], kap[i - 1])
                for x in range(kap[i], hi + 1):
                    rec(i + 1, cur + [x])
            rec(0, [])
        states = nxt
    return states.get(tuple(lam), Counter())


def lr4(lam, nu):
    """sum over eta with len<=4 of c^lam_{nu,eta}, via Weyl alternation of the
    four-variable skew Schur polynomial."""
    if not contains(lam, nu):
        return 0
    P = skew_content_polynomial(lam, nu)
    n = sum(lam) - sum(nu)
    total = 0
    for eta in partitions(n):
        if len(eta) > 4:
            continue
        e = list(eta) + [0] * (4 - len(eta))
        c = 0
        for p, s in PERMS:
            beta = tuple(e[i] + DELTA[i] - DELTA[p[i]] for i in range(4))
            if min(beta) >= 0:
                c += s * P.get(beta, 0)
        assert c >= 0
        total += c
    return total


def lr_lattice_count_small(lam, nu):
    """Brute LR tableaux with entries<=4 (lattice reverse reading word), small only."""
    cells = [(i, j) for i in range(len(lam)) for j in range(nu[i] if i < len(nu) else 0, lam[i])]
    cnt = 0
    for vals in itertools.product(range(1, 5), repeat=len(cells)):
        T = dict(zip(cells, vals))
        if any((i, j - 1) in T and T[(i, j - 1)] > T[(i, j)] for i, j in cells):
            continue
        if any((i - 1, j) in T and T[(i - 1, j)] >= T[(i, j)] for i, j in cells):
            continue
        word = [T[c] for c in sorted(cells, key=lambda c: (c[0], -c[1]))]
        seen = Counter()
        ok = True
        for x in word:
            seen[x] += 1
            if x > 1 and seen[x] > seen[x - 1]:
                ok = False
                break
        cnt += ok
    return cnt


def four_strip_predecessors(lam, n):
    """nu |- n with lam_i >= nu_i >= lam_{i+4}."""
    L = len(lam)
    out = []

    def rec(i, left, cur):
        if i == L:
            if left == 0:
                out.append(tuple(x for x in cur if x))
            return
        lo = lam[i + 4] if i + 4 < L else 0
        hi = min(lam[i], cur[-1] if cur else lam[i], left)
        for x in range(hi, lo - 1, -1):
            rec(i + 1, left - x, cur + [x])
    rec(0, n, [])
    return out


def weighted_two_band(args):
    """Two-band sum at m with the invariant weights at h=m-2 and exact LR sums."""
    m, lam = args
    h2 = m - 2
    return sum(((h2 - 1) if nu not in exceptions(h2) else 1) * lr4(lam, nu)
               for nu in four_strip_predecessors(lam, N(h2)))


# ---------- main computation ----------
def main():
    report = {'algorithm_checks': {}, 'small_squares': {}, 'exact_recursion': {},
              'boundary': {}, 'certificate_comparison': {}}

    # algorithm self-checks
    ok_k = all(kostka(l, mu) == kostka_brute(l, mu)
               for n in range(1, 8) for l in partitions(n) for mu in partitions(n))
    pairs = 0
    ok_lr = True
    for n in range(2, 9):
        for lam in partitions(n):
            for k in range(1, n):
                for nu in partitions(k):
                    if contains(lam, nu) and n - k <= 6:
                        pairs += 1
                        if lr4(lam, nu) != lr_lattice_count_small(lam, nu):
                            ok_lr = False
    orth = all(sum(Fraction(char(a, mu) * char(b, mu), zee(mu)) for mu in partitions(n)) == (a == b)
               for n in range(1, 9) for a in partitions(n) for b in partitions(n))
    dimchk = all(char(l, (1,) * n) == kostka(l, (1,) * n) for n in range(1, 10) for l in partitions(n))
    report['algorithm_checks'] = {'kostka_vs_bruteforce_n_le_7': ok_k,
                                  'lr4_vs_lattice_tableaux_pairs': pairs, 'lr4_vs_lattice_ok': ok_lr,
                                  'orthogonality_n_le_8': orth, 'dimension_eq_standard_tableaux_n_le_9': dimchk}
    assert ok_k and ok_lr and orth and dimchk

    # small squares m=2,3,4 (and sharpness through m=5)
    G = {}
    for m in (2, 3, 4, 5):
        g = kronecker_square(m)
        G[m] = g
        n = N(m)
        rest = {l: v for l, v in g.items() if l not in ((n,), (1,) * n)}
        mn = min(rest.values())
        report['small_squares'][m] = {'minimum': mn, 'minimizers': [list(l) for l, v in rest.items() if v == mn],
                                      'corner': g[(n - 1, 1)], 'trivial': g[(n,)], 'sign': g[(1,) * n]}
    for m in (2, 3, 4):
        assert report['small_squares'][m]['minimum'] == m - 1
    for m in (2, 3, 4, 5):
        assert report['small_squares'][m]['corner'] == m - 1

    # exact recursion R_m for m<=6
    R = {1: {(1,): 1}}
    rec_rows = {}
    for m in range(2, 7):
        n = N(m)
        rows = {}
        for lam in partitions(n):
            K = kostka(conj(lam), stair(m))
            one = sum(R[m - 1].get(nu, 0) for nu in strips_below(lam, m))
            two = 0
            if m >= 3:
                for nu in four_strip_predecessors(lam, N(m - 2)):
                    two += R[m - 2][nu] * lr4(lam, nu)
            rows[lam] = (K, one, two, max(1, K, one, two))
        R[m] = {l: v[3] for l, v in rows.items()}
        rec_rows[m] = rows
        if m >= 5:
            bad = [l for l, v in R[m].items() if l not in exceptions(m) and v < m - 1]
            assert not bad, (m, bad[:5])
            nonexc = [v for l, v in R[m].items() if l not in exceptions(m)]
            report['exact_recursion'][m] = {'labels': len(R[m]), 'nonexceptional': len(nonexc),
                                            'min_nonexceptional': min(nonexc),
                                            'exception_values': {str(l if len(l) < 8 else 'len%d:%s' % (len(l), l[:3])): R[m][l]
                                                                 for l in sorted(exceptions(m))}}
        # range sanity vs actual squares where computed (stipulated contracts; not a proof input)
        if m in G:
            assert all(max(R[m][l], R[m][conj(l)]) <= G[m][l] for l in R[m])

    # boundary m=7,8 using the invariant at m-1, m-2 (weights h-1 / 1)
    for m in (7, 8):
        n, h1, h2 = N(m), m - 1, m - 2
        stats = Counter()
        crit = (m, m - 2) + (1,) * (n - 2 * m + 2)
        remaining = []
        for lam in partitions(n):
            if lam in exceptions(m):
                continue
            preds = strips_below(lam, m)
            one = sum((h1 - 1) if nu not in exceptions(h1) else 1 for nu in preds)
            if one >= m - 1:
                stats['one'] += 1
                continue
            if kostka(conj(lam), stair(m)) >= m - 1:
                stats['K'] += 1
                continue
            remaining.append(lam)
        with multiprocessing.Pool(12) as pool:
            values = pool.map(weighted_two_band, [(m, lam) for lam in remaining], chunksize=4)
        for lam, two in zip(remaining, values):
            assert two >= m - 1, (m, lam, two)
        stats['two_exact_LR'] = len(remaining)
        min_two = min(values)
        crit_value = dict(zip(remaining, values)).get(crit)
        crit_nu = (2,) + (1,) * (N(h2) - 2)
        report['boundary'][m] = {'labels': len(partitions(n)), 'stats': dict(stats),
                                 'critical_label_weighted_two_band': crit_value,
                                 'critical_nu_lr4': lr4(crit, crit_nu),
                                 'min_two_band_on_remaining': min_two}

    # entrywise comparison with the author certificate (after recomputation)
    cert = json.loads(CERT.read_text())
    sq_ok = True
    for blk in cert['small_squares']:
        m = blk['m']
        for row in blk['coefficients']:
            if G[m][tuple(row['lambda'])] != row['g']:
                sq_ok = False
    rec_ok, rec_n = True, 0
    for blk in cert['cyclic_recursion']:
        m = blk['m']
        for e in blk['entries']:
            rec_n += 1
            if rec_rows[m][tuple(e['lambda'])] != (e['K'], e['one'], e['two'], e['R']):
                rec_ok = False
    bnd = {}
    for blk in cert['boundary']:
        m = blk['m']
        st = report['boundary'][m]['stats']
        bnd[m] = {'cert_stats': blk['stats'], 'cert_eligible': blk['eligible'],
                  'reviewer_one': st.get('one'), 'reviewer_K': st.get('K'),
                  'reviewer_two_exact': st.get('two_exact_LR'),
                  'match': (blk['stats'].get('one') == st.get('one') and blk['stats'].get('K') == st.get('K') and
                            blk['stats'].get('four-strip', 0) + blk['stats'].get('critical-LR-formula', 0)
                            == st.get('two_exact_LR'))}
    report['certificate_comparison'] = {'small_square_entries_equal': sq_ok,
                                        'recursion_entries_equal': rec_ok, 'recursion_entries': rec_n,
                                        'boundary': bnd}
    assert sq_ok and rec_ok and all(v['match'] for v in bnd.values())
    report['result'] = 'PASS_REVIEWER_INDEPENDENT_FINITE'
    print(json.dumps(report, indent=1, sort_keys=True, default=str))


if __name__ == '__main__':
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))
    sys.setrecursionlimit(10000)
    main()
