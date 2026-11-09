"""Independent jeu-de-taquin deletion and k-minor multisets (reviewer r1, 2026-11-02).

Written from the source definition (arXiv:2307.13161, Section 2), not from the lane code.
A tableau is a tuple of row tuples (English convention), entries 1..n.
"""
from collections import Counter


def is_syt(T, n):
    if any(len(r) == 0 for r in T):
        return False
    if any(len(T[i + 1]) > len(T[i]) for i in range(len(T) - 1)):
        return False
    for r in T:
        if any(r[j] >= r[j + 1] for j in range(len(r) - 1)):
            return False
    for i in range(len(T) - 1):
        for j in range(len(T[i + 1])):
            if T[i][j] >= T[i + 1][j]:
                return False
    return sorted(x for r in T for x in r) == list(range(1, n + 1))


def delete(T, m):
    """T - m: remove cell m, slide the smaller of right/below neighbours into the hole
    until the hole is an outer corner, drop it, then decrement entries > m."""
    g = {}
    for i, r in enumerate(T):
        for j, x in enumerate(r):
            g[(i, j)] = x
    pos = [p for p, x in g.items() if x == m]
    assert len(pos) == 1
    hole = pos[0]
    del g[hole]
    while True:
        i, j = hole
        right, below = g.get((i, j + 1)), g.get((i + 1, j))
        if right is None and below is None:
            break
        if below is None or (right is not None and right < below):
            nxt = (i, j + 1)
        else:
            nxt = (i + 1, j)
        g[hole] = g.pop(nxt)
        hole = nxt
    rows = {}
    for (i, j), x in g.items():
        rows.setdefault(i, {})[j] = x - 1 if x > m else x
    out = []
    for i in range(len(rows)):
        r = rows[i]
        out.append(tuple(r[j] for j in range(len(r))))
    out = tuple(out)
    assert is_syt(out, sum(len(r) for r in T) - 1), (T, m, out)
    return out


def size(T):
    return sum(len(r) for r in T)


def minors_multiset(T, k):
    """mM_k(T) as a Counter, by a weighted level DP over deletion sequences."""
    level = Counter({T: 1})
    for _ in range(k):
        nxt = Counter()
        for S, w in level.items():
            for m in range(1, size(S) + 1):
                nxt[delete(S, m)] += w
        level = nxt
    return level


def all_syt(n):
    """All SYT of size n, by adding the entry n at an addable cell of an SYT of size n-1."""
    cur = [()]
    for v in range(1, n + 1):
        nxt = []
        for T in cur:
            rows = [list(r) for r in T]
            for i in range(len(rows) + 1):
                if i == len(rows):
                    nxt.append(tuple(tuple(r) for r in rows) + ((v,),))
                elif i == 0 or len(rows[i]) < len(rows[i - 1]):
                    new = [tuple(r) for r in rows]
                    new[i] = new[i] + (v,)
                    nxt.append(tuple(new))
        cur = nxt
    return cur


def transpose(T):
    return tuple(tuple(T[i][j] for i in range(len(T)) if j < len(T[i])) for j in range(len(T[0])))


def hook(arm, n):
    """Hook with first row `arm` (contains 1) and first column 1 plus the rest of 1..n."""
    leg = [x for x in range(2, n + 1) if x not in arm]
    return (tuple(sorted(arm)),) + tuple((x,) for x in leg)
