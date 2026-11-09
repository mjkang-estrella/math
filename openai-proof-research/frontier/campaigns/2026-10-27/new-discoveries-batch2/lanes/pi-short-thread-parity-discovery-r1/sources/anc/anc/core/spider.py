"""
Specialised solver for the Game of Arrows on spiders (one branch vertex, any number of legs).

Coupled state: (center label in {N,I,O}, sorted tuple of attached legs (r, f)),
r >= 1 = number of unmarked edges between the centre and the first marked edge (or the
trimmed leaf), f in {'F','T','A'}: far end free (trimmed leaf), or forced Toward/Away
from the centre by the nearest marked edge on that leg.
Detached runs are evaluated with the closed forms
   A_k = k mod 2 (free/free), B_k = k (free/forced), C_k = k mod 2 (coherent forced),
   D_k = 1 if k even and k >= 2 else 0 (incoherent forced),
which are verified numerically in runs.py and proved in the paper.
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)


def A(k):
    return k & 1


def B(k):
    return k


def C(k):
    return k & 1


def D(k):
    return 1 if (k >= 2 and k % 2 == 0) else 0


def run(k, near, far):
    """Detached run of k cells; near in {'F','T','A'} (F = free), far in {'F','T','A'}."""
    if k == 0:
        return 0
    if near == 'F' and far == 'F':
        return A(k)
    if near == 'F' or far == 'F':
        return B(k)
    return C(k) if near == far else D(k)


def mex(s):
    g = 0
    while g in s:
        g += 1
    return g


def settle(label, legs):
    """Normalise a coupled state. Returns (extra_value, key or None)."""
    legs = tuple(sorted(legs))
    if label == 'F':
        x = 0
        for (r, f) in legs:
            x ^= run(r, 'F', f)
        return x, None
    if len(legs) == 0:
        return 0, None
    if len(legs) == 1 and label in ('I', 'O'):
        r, f = legs[0]
        near = 'A' if label == 'I' else 'T'   # remaining centre edge must point away / toward
        return run(r, near, f), None
    return 0, (label, legs)


@lru_cache(maxsize=None)
def coupled(label, legs):
    opts = set()
    deg = len(legs)
    for i, (r, f) in enumerate(legs):
        others = legs[:i] + legs[i + 1:]
        for j in range(1, r + 1):
            for d in ('T', 'A'):
                if j == r and f != 'F' and d != f:
                    continue
                if j == 1 and deg == 1:
                    if not ((label == 'I' and d == 'A') or (label == 'O' and d == 'T')):
                        continue
                det = run(r - j, d, f)
                if j >= 2:
                    nl = label
                    nlegs = others + ((j - 1, d),)
                else:
                    if d == 'T':
                        nl = {'N': 'I', 'I': 'I', 'O': 'F'}[label]
                    else:
                        nl = {'N': 'O', 'O': 'O', 'I': 'F'}[label]
                    nlegs = others
                x, key = settle(nl, nlegs)
                val = det ^ x ^ (coupled(*key) if key else 0)
                opts.add(val)
    return mex(opts)


def spider_value(legs_original):
    """legs_original: leg lengths in edges of the original tree (each >= 1)."""
    if any(L == 1 for L in legs_original):
        # centre adjacent to a leaf: centre is special (free)
        x = 0
        for L in legs_original:
            if L >= 2:
                x ^= A(L - 1)
        return x
    x, key = settle('N', tuple((L - 1, 'F') for L in legs_original))
    return x ^ (coupled(*key) if key else 0)


if __name__ == "__main__":
    legs = tuple(int(a) for a in sys.argv[1:])
    print(legs, spider_value(legs))
