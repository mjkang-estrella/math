# Check Conjecture 1.2 of arXiv:2506.07264 (MathDB 368742): connected G, m >= n+1 => s+(G) >= n,
# on every connected graph with m = n-1+c obtained from a unicyclic graph (any cycle length, all
# isomorphism classes) by adding c-1 non-edges.  Every connected graph with cyclomatic number c >= 2
# contains a spanning unicyclic subgraph, so this covers ALL connected graphs with m = n+c-1 at that n
# (with repetitions).  Also records, among cases, the minimum of s+(G) - n.
import sys, itertools, json, numpy as np
sys.argv_saved = list(sys.argv)
NMAX = int(sys.argv[1]); NMIN = int(sys.argv[2]); EXTRA = int(sys.argv[3])  # EXTRA = c-1 edges to add
src = open(__file__.replace('strong_positive.py', 'unicyclic.py')).read()
pre = src.split('out = {}')[0]
exec(pre.replace('NMAX = int(sys.argv[1]); NMIN = int(sys.argv[2]) if len(sys.argv) > 2 else 3', f'NMAX={NMAX}; NMIN={NMIN}'))
res = {}
for n in range(NMIN, NMAX + 1):
    best = (1e9, None); total = 0; viol = 0
    for k in range(3, n + 1):
        for comp in compositions(n, k):
            for choice in itertools.product(*[range(len(trees[a])) for a in comp]):
                seq = tuple(zip(comp, choice))
                if canon(seq) != seq: continue
                edges = [(j, (j + 1) % k) for j in range(k)]; nxt = k
                for j, (a, i) in enumerate(seq): nxt = tree_edges(a, i, j, nxt, edges)
                A = np.zeros((n, n))
                for u, v in edges: A[u, v] = A[v, u] = 1
                non = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u, v] == 0]
                batch = []
                for add in itertools.combinations(non, EXTRA):
                    B = A.copy()
                    for u, v in add: B[u, v] = B[v, u] = 1
                    batch.append(B)
                if not batch: continue
                ev = np.linalg.eigvalsh(np.array(batch))
                sp = (np.where(ev > 0, ev, 0) ** 2).sum(axis=1) - n
                total += len(batch); j = int(np.argmin(sp))
                viol += int((sp < -1e-9).sum())
                if sp[j] < best[0]: best = (float(sp[j]), (k, repr(seq), [list(map(int, np.argwhere(np.triu(batch[j] - A))[t])) for t in range(EXTRA)]))
    res[n] = dict(graphs_with_repetition=total, min_splus_minus_n=best[0], argmin=best[1], violations=viol)
    print(n, total, round(best[0], 6), viol, best[1], flush=True)
json.dump(res, open(sys.argv[4], 'w'), indent=1)
