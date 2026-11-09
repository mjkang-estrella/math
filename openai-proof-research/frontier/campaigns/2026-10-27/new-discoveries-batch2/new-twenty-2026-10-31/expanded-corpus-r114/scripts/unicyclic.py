# Exhaustive enumeration of unicyclic graphs with odd cycle length k (up to isomorphism),
# as a cycle C_k with rooted trees hanging at cycle vertices, canonical up to dihedral symmetry.
# For each graph computes D = s+(G) - n = (s+ - s-)/2 (since s+ + s- = 2m = 2n) and checks
# Conjecture 9.1 of arXiv:2506.07264 (MathDB 368743): D>0 if k = 3 mod 4, D<0 if k = 1 mod 4.
import sys, json, itertools, numpy as np
from functools import lru_cache

NMAX = int(sys.argv[1]); NMIN = int(sys.argv[2]) if len(sys.argv) > 2 else 3

# rooted trees by size, as canonical nested tuples (sorted children)
trees = {1: [()]}
def partitions_children(total, maxkey):
    # multisets of rooted trees with total size `total`, children ordered nonincreasingly by (size, index)
    if total == 0:
        yield ()
        return
    for s in range(min(total, maxkey[0]), 0, -1):
        lst = trees[s]
        hi = min(maxkey[1], len(lst) - 1) if s == maxkey[0] else len(lst) - 1
        for i in range(hi, -1, -1):
            for rest in partitions_children(total - s, (s, i)):
                yield ((s, i),) + rest
for s in range(2, NMAX + 1):
    trees[s] = list(partitions_children(s - 1, (s - 1, 10**9)))

def tree_edges(s, i, root, nxt, edges):
    # expand tree (s,i) rooted at vertex `root`; returns next free label
    for (cs, ci) in trees[s][i]:
        v = nxt; nxt += 1; edges.append((root, v))
        nxt = tree_edges(cs, ci, v, nxt, edges)
    return nxt

def compositions(n, k):
    if k == 1:
        yield (n,); return
    for a in range(1, n - k + 2):
        for rest in compositions(n - a, k - 1):
            yield (a,) + rest

def canon(seq):
    k = len(seq); best = None
    for r in range(k):
        for d in (1, -1):
            t = tuple(seq[(r + d * j) % k] for j in range(k))
            if best is None or t < best: best = t
    return best

out = {}
viol = []
for n in range(NMIN, NMAX + 1):
    stats = {}
    for k in range(3, n + 1, 2):
        mats = []; labels = []
        for comp in compositions(n, k):
            for choice in itertools.product(*[range(len(trees[a])) for a in comp]):
                seq = tuple(zip(comp, choice))
                if canon(seq) != seq: continue
                edges = [(j, (j + 1) % k) for j in range(k)]; nxt = k
                for j, (a, i) in enumerate(seq):
                    nxt = tree_edges(a, i, j, nxt, edges)
                A = np.zeros((n, n))
                for u, v in edges: A[u, v] = A[v, u] = 1
                mats.append(A); labels.append(seq)
        if not mats: continue
        ev = np.linalg.eigvalsh(np.array(mats))
        D = (ev * np.abs(ev)).sum(axis=1) / 2
        want = 1 if k % 4 == 3 else -1
        bad = np.where(D * want <= 1e-9)[0]
        worst = int(np.argmin(D * want))
        stats[k] = dict(count=len(mats), min_signed_margin=float(D[worst] * want), worst=repr(labels[worst]), violations=int(len(bad)))
        for b in bad[:20]:
            viol.append(dict(n=n, k=k, D=float(D[b]), seq=repr(labels[b])))
    out[n] = stats
    print(n, {k: (v['count'], round(v['min_signed_margin'], 6), v['violations']) for k, v in stats.items()}, flush=True)
json.dump(dict(results=out, violations=viol[:200]), open(sys.argv[3] if len(sys.argv) > 3 else '/dev/null', 'w'), indent=1)
print('violations', len(viol))
for v in viol[:10]: print(v)
