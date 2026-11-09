"""Explicit family refuting Das (arXiv:2112.00442v3) Conjecture 5.1 for every n >= 5.

Vertices (0-based): x=0, x'=1, y=2, y'=3, s_1..s_m = 4..n-1 (m = n-4 >= 0).
  '+' : x<->x', y<->y', x->s_i, s_i->y                       (2m+4 entries)
  '-' : return path y'->s_m->...->s_1->x' and every mirror   (2(m+1) entries)
Total 4n-10 nonzeros.  This script checks AP-irreducibility and minimality by
brute force (independent of the proof in discovery.md), and optionally runs a
local search seeded at the family to look for larger minimal patterns.
Usage: apfamily.py verify NMAX   |  apfamily.py improve N ITERS SEED
"""
import sys, json, random, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from apirr import ap_irr, minimal, reduce_random, show


def family(n):
    assert n >= 4
    x, xp, y, yp = 0, 1, 2, 3
    s = list(range(4, n))
    A = {(x, xp): 1, (xp, x): 1, (y, yp): 1, (yp, y): 1}
    for v in s:
        A[(x, v)] = 1
        A[(v, y)] = 1
    path = [yp] + s[::-1] + [xp]
    for u, v in zip(path, path[1:]):
        assert (u, v) not in A and (v, u) not in A
        A[(u, v)] = -1
        A[(v, u)] = -1
    return A


if __name__ != '__main__':
    pass
elif sys.argv[1] == 'verify':
    rows = []
    for n in range(4, int(sys.argv[2]) + 1):
        A = family(n)
        ok = ap_irr(n, A) and minimal(n, A) and all(i != j for i, j in A)
        rows.append({'n': n, 'nonzeros': len(A), '4n-10': 4 * n - 10, '2n-2': 2 * n - 2, 'ap_irreducible_and_minimal': ok})
        assert ok and len(A) == 4 * n - 10
    print(json.dumps(rows))
    print('\n'.join(show(5, family(5))))
    print()
    print('\n'.join(show(7, family(7))))
else:
    n, iters, seed = map(int, sys.argv[2:5])
    rng = random.Random(seed)
    cells = [(i, j) for i in range(n) for j in range(n) if i != j]
    cur = family(n); best = dict(cur)
    for t in range(iters):
        B = dict(cur)
        for c in rng.sample(cells, rng.randint(1, n)):
            B[c] = rng.choice((1, -1))
        if not ap_irr(n, B):
            continue
        B = reduce_random(n, B, rng)
        if len(B) >= len(cur) - (1 if rng.random() < 0.1 else 0):
            cur = B
        if len(cur) > len(best):
            best = dict(cur)
            print('improved', len(best), show(n, best), flush=True)
    assert ap_irr(n, best) and minimal(n, best)
    print(json.dumps({'n': n, 'iters': iters, 'seed': seed, 'best': len(best), '4n-10': 4 * n - 10, 'pattern': show(n, best)}))
