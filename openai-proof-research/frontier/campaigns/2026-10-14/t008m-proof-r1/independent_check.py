#!/usr/bin/env python3
"""Reviewer-side finite cross-check for T008M, written independently of the
author's diagnostic-008.py.  Finite evidence only; it is not the proof.
Standard library only.  Original code: MIT.

Checks
  1. every X_d is a 0/1 partial-permutation matrix, raising level by exactly d;
  2. dense integer matrix products X_{d1}...X_{dk} (row-to-column) agree with
     deterministic path following, and kill all words of weight > cap;
  3. for every top word w, the extracting entry is 1 for w and 0 for every
     other word of every weight 0..cap+4;
  4. the three-cap direct sum has rank dim A_N on the WHOLE inhomogeneous
     truncated algebra A_N over Q, GF(2) and GF(3);
  5. exact state counts, a_j <= rho^j, and D_T <= K rho^(T/2) up to large T;
  6. exact Witt dimensions l_n via Lyndon enumeration and Mobius inversion,
     and the explicit threshold n>=36 for l_n >= rho^n/(2n) (finite part);
  7. reviewer mutation controls that must FAIL.
"""
import json, math, sys
from fractions import Fraction
from functools import lru_cache

LETTERS_UPTO = lambda n: list(range(3, n + 1, 2))


@lru_cache(None)
def words_of_weight(k, dup3=False):
    """All words (tuples of letters) of weight exactly k.  dup3 adds a second
    weight-3 letter labelled -3 (mutation: two generators in one weight)."""
    if k == 0:
        return ((),)
    out = []
    alphabet = LETTERS_UPTO(k) + ([-3] if dup3 and k >= 3 else [])
    for d in alphabet:
        for v in words_of_weight(k - abs(d), dup3):
            out.append((d,) + v)
    return tuple(out)


def wt(w):
    return sum(abs(x) for x in w)


def build(cap, mutation=None, dup3=False):
    m = 1 if cap == 1 else cap // 2
    b = cap - m
    P = [('P', a, r) for j in range(m) for a in words_of_weight(j, dup3) for r in range(1, m - j + 1)]
    Q = [('Q', v, s) for j in range(b + 1) for v in words_of_weight(j, dup3) for s in range(0, b - j + 1)]
    lev = {}
    for st in P:
        lev[st] = -(wt(st[1]) + st[2])
    for st in Q:
        lev[st] = wt(st[1]) + st[2]
    order = sorted(P + Q, key=lambda x: (lev[x], repr(x)))
    idx = {s: i for i, s in enumerate(order)}
    Pset, Qset = set(P), set(Q)
    letters = LETTERS_UPTO(cap + 4) + ([-3] if dup3 else [])
    X = {}
    for d in letters:
        dd = abs(d)
        edges = []
        for st in P:
            _, a, r = st
            if a and a[0] == d:                      # prefix deletion
                edges.append((st, ('P', a[1:], r)))
            if not a:                                 # crossing
                s = dd - r
                if mutation == 'gap_sign_flip':
                    s = r - dd
                if s >= 0 and ('Q', (), s) in Qset:
                    edges.append((st, ('Q', (), s)))
        for st in Q:
            _, v, s = st
            tgt = ('Q', (d,) + v, s) if mutation == 'prepend_suffix' else ('Q', v + (d,), s)
            if tgt in Qset:
                edges.append((st, tgt))
            if mutation == 'allow_Q_to_P' and not v:
                r = dd - s if dd > s else None
                if r is not None and ('P', (), r) in Pset:
                    edges.append((st, ('P', (), r)))
        X[d] = edges
    return dict(m=m, b=b, order=order, idx=idx, lev=lev, X=X, P=P, Q=Q)


def dense(B, d):
    n = len(B['order'])
    M = [[0] * n for _ in range(n)]
    for s, t in B['X'][d]:
        M[B['idx'][s]][B['idx'][t]] += 1
    return M


def matmul(A, C):
    n = len(A)
    Ct = list(zip(*C))
    return [[sum(x * y for x, y in zip(A[i], Ct[j])) for j in range(n)] for i in range(n)]


def image(B, w):
    """Sparse image Phi(w) as {(row,col): coefficient}, via sparse products."""
    n = len(B['order'])
    cur = {(i, i): 1 for i in range(n)}
    for d in w:
        step = {}
        for s, t in B['X'][d]:
            step.setdefault(B['idx'][s], []).append(B['idx'][t])
        nxt = {}
        for (i, j), c in cur.items():
            for k in step.get(j, []):
                nxt[(i, k)] = nxt.get((i, k), 0) + c
        cur = {k: v for k, v in nxt.items() if v}
    return cur


def extracting_entry(B, w):
    m, b = B['m'], B['b']
    acc = 0
    for i, d in enumerate(w):
        if acc + abs(d) >= m:
            a, v = w[:i], w[i + 1:]
            return B['idx'][('P', a, m - acc)], B['idx'][('Q', v, b - wt(v))]
        acc += abs(d)
    raise AssertionError('no crossing letter')


def rank(rows, p=None):
    piv = {}
    r = 0
    for row in rows:
        row = {k: (Fraction(v) if p is None else v % p) for k, v in row.items()}
        row = {k: v for k, v in row.items() if v}
        while row:
            k = min(row)
            if k not in piv:
                piv[k] = row
                r += 1
                break
            pr = piv[k]
            f = row[k] / pr[k] if p is None else row[k] * pow(pr[k], -1, p) % p
            for kk, vv in pr.items():
                nv = row.get(kk, 0) - f * vv
                if p is not None:
                    nv %= p
                if nv:
                    row[kk] = nv
                else:
                    row.pop(kk, None)
    return r


def caps_rank(N, p=None, caps=None, mutation=None):
    caps = caps or [N - 2, N - 1, N]
    blocks = [(T, build(T, mutation)) for T in caps]
    allw = [w for k in range(N + 1) for w in words_of_weight(k)]
    rows = []
    for w in allw:
        row = {}
        for T, B in blocks:
            for (i, j), c in image(B, w).items():
                row[(T, i, j)] = c
        rows.append(row)
    return rank(rows, p), len(allw)


RHO = None


def rho():
    lo, hi = 1.0, 2.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if mid ** 3 - mid - 1 > 0:
            hi = mid
        else:
            lo = mid
    return lo


def mobius(n):
    res, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            res = -res
        p += 1
    return -res if n > 1 else res


def main():
    rep = {}
    # 1+2: matrix structure and dense product orientation
    struct = []
    for cap in range(1, 15):
        B = build(cap)
        for d, edges in B['X'].items():
            rows = [s for s, _ in edges]
            cols = [t for _, t in edges]
            assert len(rows) == len(set(rows)) and len(cols) == len(set(cols))
            for s, t in edges:
                assert B['lev'][t] - B['lev'][s] == d
                assert B['idx'][t] > B['idx'][s]
                assert not (s[0] == 'Q' and t[0] == 'P')
            if d > cap:
                assert not edges
        struct.append({'cap': cap, 'dimension': len(B['order'])})
        if cap <= 11:
            Ds = {d: dense(B, d) for d in B['X']}
            for k in range(0, cap + 4):
                for w in words_of_weight(k):
                    n = len(B['order'])
                    M = [[int(i == j) for j in range(n)] for i in range(n)]
                    for d in w:
                        M = matmul(M, Ds[d])
                    sp = {(i, j): M[i][j] for i in range(n) for j in range(n) if M[i][j]}
                    assert sp == image(B, w), (cap, w)
                    assert all(v == 1 for v in sp.values())
                    if k > cap:
                        assert not sp
    rep['structure_and_dense_products'] = struct
    # 3: extraction against every word of every weight 0..cap+4
    ext = []
    for cap in range(1, 23):
        B = build(cap)
        ims = {w: image(B, w) for k in range(cap + 5) for w in words_of_weight(k)}
        for w in words_of_weight(cap):
            e = extracting_entry(B, w)
            for u, im in ims.items():
                assert im.get(e, 0) == (1 if u == w else 0), (cap, w, u)
        ext.append({'cap': cap, 'top_words': len(words_of_weight(cap)), 'competitor_words': len(ims)})
    rep['extraction'] = ext
    # 4: full inhomogeneous faithfulness over Q, GF(2), GF(3)
    fr = []
    for N in range(3, 23):
        rq, dim = caps_rank(N)
        r2, _ = caps_rank(N, 2)
        r3, _ = caps_rank(N, 3)
        assert rq == r2 == r3 == dim
        fr.append({'N': N, 'dim_A_N': dim, 'rank_Q': rq, 'rank_GF2': r2, 'rank_GF3': r3})
    rep['three_cap_full_rank'] = fr
    # 5: counts and bounds
    r = rho()
    K = (r + r ** 2.5) / (r - 1) ** 2
    a = [1, 0, 0]
    for j in range(3, 401):
        a.append(a[j - 2] + a[j - 3])
    for j in range(40):
        assert a[j] == len(words_of_weight(j))
    for j in range(401):
        assert a[j] <= r ** j * (1 + 1e-12)
    for cap in range(1, 23):
        B = build(cap)
        m, b = B['m'], B['b']
        assert len(B['P']) == sum((m - j) * a[j] for j in range(m))
        assert len(B['Q']) == sum((b - j + 1) * a[j] for j in range(b + 1))
    worst = 0.0
    for T in range(2, 400):
        m, b = T // 2, T - T // 2
        D = sum((m - j) * a[j] for j in range(m)) + sum((b - j + 1) * a[j] for j in range(b + 1))
        worst = max(worst, D / r ** (T / 2))
        assert D <= K * r ** (T / 2)
    rep['dimension_bound'] = {'rho': r, 'K': K, 'max_D_T_over_rho^(T/2)_T_2..399': worst}
    # 6: Witt dimensions and explicit lower threshold
    tr = [3, 0, 2]
    for n in range(3, 201):
        tr.append(tr[n - 2] + tr[n - 3])
    qn = [None] + [tr[n] - 1 - (-1) ** n for n in range(1, 201)]
    l = [None]
    for n in range(1, 201):
        num = sum(mobius(d) * qn[n // d] for d in range(1, n + 1) if n % d == 0)
        assert num % n == 0
        l.append(num // n)
    for n in range(1, 21):
        ly = sum(1 for w in words_of_weight(n)
                 if all(w < w[i:] + w[:i] for i in range(1, len(w))))
        assert ly == l[n], (n, ly, l[n])
    for n in range(1, 201):
        assert abs(qn[n] - r ** n) <= 4 + 1e-6 * r ** n
    first = min(n for n in range(8, 200) if r ** (n / 2) >= 4 * n)
    assert first == 36
    for n in range(36, 201):
        assert l[n] >= r ** n / (2 * n)
    holds = [n for n in range(3, 201) if l[n] >= r ** n / (2 * n)]
    rep['witt'] = {'analytic_threshold_rho^(n/2)>=4n_from': first,
                   'l_n>=rho^n/(2n)_fails_for_n_in_3..200': [n for n in range(3, 201) if n not in holds]}
    # 7: mutation controls must fail
    mut = {}
    # two generators in weight 3: extraction entry sees both crossing letters
    B = build(9, dup3=True)
    w1, w2 = (3, 3, 3), (3, -3, 3)
    e = extracting_entry(B, w1)
    mut['two_generators_weight3'] = {'entry_w1': image(B, w1).get(e, 0), 'entry_w2_same_entry': image(B, w2).get(e, 0)}
    assert mut['two_generators_weight3']['entry_w2_same_entry'] == 1  # failure of uniqueness: entry also sees w2
    for name in ['gap_sign_flip', 'prepend_suffix', 'allow_Q_to_P']:
        bad = 0
        # suffixes of weight <= 7 are all palindromes, so caps reach 19
        for cap in range(3, 20):
            B = build(cap, name)
            for w in words_of_weight(cap):
                try:
                    e = extracting_entry(B, w)
                except KeyError:
                    bad += 1
                    continue
                ims = [image(B, u).get(e, 0) for u in words_of_weight(cap)]
                if image(B, w).get(e, 0) != 1 or sum(1 for x in ims if x) != 1:
                    bad += 1
            # allow_Q_to_P also breaks strict upper-triangularity / weight cutoff
        if name == 'allow_Q_to_P':
            B = build(9, name)
            longw = (3,) * 7
            bad += int(bool(image(B, longw)))
        mut[name] = {'extraction_failures_or_cutoff_violations': bad}
        assert bad > 0
    rep['mutations_detected'] = mut
    # Reviewer observation (optional objection O1): one cap is already faithful,
    # because the cut can be placed at m'=min(m,k) for every weight 1<=k<=T.
    single = []
    for N in range(1, 23):
        rq, dim = caps_rank(N, caps=[N])
        r2, _ = caps_rank(N, 2, caps=[N])
        assert rq == r2 == dim
        single.append({'N': N, 'dim_A_N': dim, 'rank_Q': rq, 'rank_GF2': r2})
    rep['single_cap_full_rank'] = single
    sub = 0
    for T in range(1, 19):
        B = build(T)
        m, b = B['m'], B['b']
        ims = {w: image(B, w) for k in range(T + 1) for w in words_of_weight(k)}
        for k in range(1, T + 1):
            mp = min(m, k)
            bp = k - mp
            assert 1 <= mp <= m and 0 <= bp <= b
            for w in words_of_weight(k):
                acc = 0
                for i, d in enumerate(w):
                    if acc + d >= mp:
                        a, v = w[:i], w[i + 1:]
                        e = (B['idx'][('P', a, mp - acc)], B['idx'][('Q', v, bp - wt(v))])
                        break
                    acc += d
                for u, im in ims.items():
                    assert im.get(e, 0) == (1 if u == w else 0)
                sub += 1
    rep['sub_level_extraction_words_checked'] = sub
    rep['status'] = 'PASS_REVIEWER_FINITE_CROSSCHECK_NOT_PROOF'
    print(json.dumps(rep, indent=1, default=str))


if __name__ == '__main__':
    main()
