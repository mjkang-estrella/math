"""371619 diagnostic (Chen-Liu-Qi-Yang arXiv:2511.17000 Conjecture 7.1).
Items = (edge of K_n, colour in [s]); a configuration G_1..G_s = set of present items.
Forbidden: an (r-1)-star edge-coloured K_r: an r-set W and a colouring of the edges of K_W
using exactly r-1 colours from [s], every colour class a star (K_{1,m}, m >= 1), all items present.
Max total edges = s*C(n,2) - tau, tau = minimum hitting set of forbidden item sets.
Conjecture fails iff tau < s*C(n,2) - s*t(n,r-1).  Exact search by bounded branching.
usage: starturan.py r s n [cap]
"""
import sys, itertools
r, s, n = map(int, sys.argv[1:4])
cap = int(sys.argv[4]) if len(sys.argv) > 4 else None

def turan(n, k):
    q, rem = divmod(n, k)
    parts = [q + 1] * rem + [q] * (k - rem)
    return (n * n - sum(p * p for p in parts)) // 2

E = list(itertools.combinations(range(n), 2))
eid = {e: i for i, e in enumerate(E)}
item = lambda e, c: eid[e] * s + c

def is_star(edges):
    common = set(edges[0])
    for e in edges[1:]:
        common &= set(e)
    return len(common) >= 1

# template colourings of K_r on vertices 0..r-1
TE = list(itertools.combinations(range(r), 2))
templates = []
for col in itertools.product(range(s), repeat=len(TE)):
    used = set(col)
    if len(used) != r - 1:
        continue
    if all(is_star([TE[i] for i in range(len(TE)) if col[i] == c]) for c in used):
        templates.append(col)
hyper = set()
for W in itertools.combinations(range(n), r):
    for col in templates:
        hyper.add(frozenset(item((W[a], W[b]), col[i]) for i, (a, b) in enumerate(TE)))
hyper = [tuple(sorted(h)) for h in hyper]
N_items = len(E) * s
bound = s * turan(n, r - 1)
need = N_items - bound  # conjecture holds iff tau >= need
print(f'r={r} s={s} n={n} items={N_items} forbidden={len(hyper)} templates={len(templates)} conj_bound={bound} need_tau>={need}')

sys.setrecursionlimit(10000)
nodes = 0
def hit(k, removed):
    """is there a hitting set of size <= k extending removed?"""
    global nodes
    nodes += 1
    unhit = [h for h in hyper if not any(x in removed for x in h)]
    if not unhit:
        return set(removed)
    if k == 0:
        return None
    # lower bound: greedy packing of pairwise disjoint unhit hyperedges
    used = set(); pack = 0
    for g in unhit:
        if not any(x in used for x in g):
            used.update(g); pack += 1
            if pack > k:
                return None
    # branch on the unhit hyperedge whose items are most frequent among unhit (fewest effective)
    freq = {}
    for g in unhit:
        for x in g:
            freq[x] = freq.get(x, 0) + 1
    h = min(unhit, key=lambda g: -sum(freq[x] for x in g))
    for x in sorted(h, key=lambda x: -freq[x]):
        removed.add(x)
        res = hit(k - 1, removed)
        removed.discard(x)
        if res is not None:
            return res
    return None

K = need - 1 if cap is None else min(cap, need - 1)
res = hit(K, set())
if res is None:
    print(f'no hitting set of size <= {K}: tau >= {K+1}; nodes={nodes}', 'conjecture holds here' if K == need - 1 else 'partial')
else:
    print('COUNTEREXAMPLE hitting set size', len(res), sorted((E[x // s], x % s) for x in res), 'total edges', N_items - len(res), '>', bound)
