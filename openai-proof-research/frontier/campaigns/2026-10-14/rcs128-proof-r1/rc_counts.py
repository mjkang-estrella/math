# Independent reviewer re-implementation (rcs128-proof-r1). SPDX-License-Identifier: MIT
"""Independent implementation of the candidate's symmetric count recursion
(broad self-text 2k+1 rule, ordinary k+1 otherwise) and exact OPT_RC.

Written from candidate.md section 1 and source 02-counts.tex only; it does not
import or copy author code.  Finite diagnostics only; not a proof.
"""
from functools import lru_cache
import itertools


def make_rho(cm):
    def rho(s):
        return ''.join(cm[ch] for ch in reversed(s))
    return rho


def preprocess(words, cm):
    """Remove empties, form rho-orbits, drop orbits contained in a different orbit."""
    rho = make_rho(cm)
    orbits = {}
    for s in words:
        if not s:
            continue
        key = min(s, rho(s))
        orbits[key] = frozenset({s, rho(s)})
    reps = sorted(orbits)
    keep = []
    for x in reps:
        contained = False
        for y in reps:
            if y == x:
                continue
            if any(a in b for a in orbits[x] for b in orbits[y]):
                contained = True
                break
        if not contained:
            keep.append(x)
    R = set()
    for x in keep:
        R |= orbits[x]
    return keep, R


def is_self_text(A, cm):
    """Is rho(A^Z) a translate of A^Z?  (A = one period)"""
    rho = make_rho(cm)
    return rho(A) in (A + A)


def counts(words, cm, rule='broad'):
    """rule: 'broad' = candidate (2k+1 on self texts); 'ordinary' = k+1 everywhere."""
    rho = make_rho(cm)
    keep, R = preprocess(words, cm)
    V = {''}
    for s in R:
        for i in range(len(s)):
            for j in range(i + 1, len(s) + 1):
                V.add(s[i:j])
    alpha = sorted(set(''.join(R)))
    m = {}
    byLen = sorted((v for v in V if v), key=lambda s: (-len(s), s))
    longer = {}

    def M(s):
        return m.get(s, 0)

    # index of interior placements: s -> list of (r, j) with 1<=j, j+|s|<=|r|-1
    place = {}
    for r in V:
        lr = len(r)
        for j in range(1, lr - 1):
            for e in range(j + 1, lr):
                place.setdefault(r[j:e], []).append((r, j))

    Bcache = {}

    def B(s, A):
        # valid to cache: all words of length >= |s|+2 are final when B(s, .) is first used
        key = (s, A)
        if key not in Bcache:
            Bcache[key] = B0(s, A)
        return Bcache[key]

    def B0(s, A):
        """sum over bracket words r = x + I + y, I = A-aligned interior containing s at
        interior offset j-1 (s at r[j:j+|s|)), x != A(-j), y != A(|r|-1-j)."""
        p = len(A)
        ls = len(s)
        tot = 0
        Ach = lambda i: A[i % p]
        j = 1
        while True:
            # interior must contain A[1-j : |s|) as a word in V (left extension of s)
            left = ''.join(Ach(i) for i in range(1 - j, 0))
            if left + s not in V:
                break
            lr = j + ls + 1
            while True:
                I = left + s + ''.join(Ach(i) for i in range(ls, lr - 1 - j))
                if I not in V:
                    break
                L0, R0 = Ach(-j), Ach(lr - 1 - j)
                for x in alpha:
                    if x == L0:
                        continue
                    for y in alpha:
                        if y == R0:
                            continue
                        tot += M(x + I + y)
                lr += 1
            j += 1
        return tot

    # v -> list of extensions: index words by prefix
    by_prefix = {}
    for v in V:
        for i in range(1, len(v)):
            by_prefix.setdefault(v[:i], []).append(v)

    def bound(s):
        b = 0
        if s in R:
            b = 2 if s == rho(s) else 1
        b = max(b, sum(M(c + s) for c in alpha), sum(M(s + c) for c in alpha))
        for v in by_prefix.get(s, ()):
            for p in range(1, len(v)):
                if (len(v) - len(s)) % p:
                    continue
                if any(v[i] != v[i % p] for i in range(len(v))):
                    continue
                A = v[:p]
                k = (len(v) - len(s)) // p
                if not M(v) > B(v, A):
                    continue
                g = 2 * k + 1 if (rule == 'broad' and is_self_text(A, cm)) else k + 1
                b = max(b, B(s, A) + g)
        return b

    for s in byLen:
        if s in m:
            continue
        t = rho(s)
        val = max(bound(s), bound(t))
        if s == t and val % 2:
            val += 1
        m[s] = val
        m[t] = val
    W = sum(M(a) for a in alpha)
    return dict(keep=keep, R=R, V=V, alpha=alpha, m=m, W=W)


def overlap(a, b):
    for k in range(min(len(a), len(b)), -1, -1):
        if a[len(a) - k:] == b[:k]:
            return k
    return 0


def opt_rc(words, cm):
    """Exact OPT_RC by Held-Karp over (orbit subset, last orbit, orientation)."""
    rho = make_rho(cm)
    keep, R = preprocess(words, cm)
    if not keep:
        return 0, ''
    opts = [sorted({x, rho(x)}) for x in keep]
    n = len(opts)
    INF = 10 ** 9
    dp = {}
    for i in range(n):
        for oi, w in enumerate(opts[i]):
            dp[(1 << i, i, oi)] = (len(w), w)
    for mask in range(1, 1 << n):
        for i in range(n):
            if not mask >> i & 1:
                continue
            for oi in range(len(opts[i])):
                cur = dp.get((mask, i, oi))
                if cur is None:
                    continue
                for j in range(n):
                    if mask >> j & 1:
                        continue
                    for oj, wj in enumerate(opts[j]):
                        ov = overlap(opts[i][oi], wj)
                        cand = (cur[0] + len(wj) - ov, cur[1] + wj[ov:])
                        key = (mask | 1 << j, j, oj)
                        if key not in dp or cand[0] < dp[key][0]:
                            dp[key] = cand
    full = (1 << n) - 1
    best = min((v for (mk, i, oi), v in dp.items() if mk == full), key=lambda t: t[0])
    return best


def contains_one(T, words, cm):
    rho = make_rho(cm)
    return all((not s) or (s in T) or (rho(s) in T) for s in words)
