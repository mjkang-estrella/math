# Conjecture 4.12 of arXiv:2508.01163 (MathDB 369616): for connected G, n+(L(G)) <= n-(L(G)) + 1.
# With signless Laplacian eigenvalues theta_1..theta_n of G (n vertices, m >= n-1 edges), the spectrum of
# A(L(G)) is {theta_i - 2} plus -2 with multiplicity m - n (m >= n); for trees (m = n-1) the zero theta gives -2.
# So n+ = #{theta > 2}, n- = #{theta < 2} - [m = n-1 ... handled by formula] + (m - n), i.e. in all cases
# n- = #{i : theta_i < 2} + m - n.  Conjecture <=> #{theta>2} - #{theta<2} <= m - n + 1.
# Enumerates connected graphs with cyclomatic number c = 1 + EXTRA from all unicyclic graphs (any cycle length) by
# adding EXTRA non-edges (covers all connected graphs with that m at that n, with repetition).
import sys, itertools, json, numpy as np
NMAX = int(sys.argv[1]); NMIN = int(sys.argv[2]); EXTRA = int(sys.argv[3]); EPS = 1e-7
src = open(__file__.replace('line_inertia.py', 'unicyclic.py')).read()
exec(src.split('out = {}')[0].replace('NMAX = int(sys.argv[1]); NMIN = int(sys.argv[2]) if len(sys.argv) > 2 else 3', f'NMAX={NMAX}; NMIN={NMIN}'))
res = {}
for n in range(NMIN, NMAX + 1):
    m = n + EXTRA; c = m - n + 1; total = 0; worst = (-99, None); viol = []; near2 = 0
    for k in (range(3, n + 1) if len(sys.argv) < 6 else [int(x) for x in sys.argv[5].split(',')]):
        for comp in compositions(n, k):
            for choice in itertools.product(*[range(len(trees[a])) for a in comp]):
                seq = tuple(zip(comp, choice))
                if canon(seq) != seq: continue
                edges = [(j, (j + 1) % k) for j in range(k)]; nxt = k
                for j, (a, i) in enumerate(seq): nxt = tree_edges(a, i, j, nxt, edges)
                A = np.zeros((n, n))
                for u, v in edges: A[u, v] = A[v, u] = 1
                non = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u, v] == 0]
                combos = np.array(list(itertools.combinations(range(len(non)), EXTRA)), dtype=int).reshape(-1, EXTRA)
                if len(combos) == 0: continue
                nonarr = np.array(non); Q0 = np.diag(A.sum(axis=1)) + A
                batch = np.repeat(Q0[None], len(combos), axis=0); idx = np.arange(len(combos))
                for t in range(EXTRA):
                    u = nonarr[combos[:, t], 0]; v = nonarr[combos[:, t], 1]
                    batch[idx, u, v] = 1; batch[idx, v, u] = 1; batch[idx, u, u] += 1; batch[idx, v, v] += 1
                th = np.linalg.eigvalsh(batch); total += len(batch)
                near2 += int((np.abs(th - 2) < EPS).any(axis=1).sum())
                excess = (th > 2 + EPS).sum(axis=1) - (th < 2 - EPS).sum(axis=1) - c
                j = int(np.argmax(excess))
                if excess[j] > worst[0]: worst = (int(excess[j]), (k, repr(seq)))
                for b in np.nonzero(excess > 0)[0][:5]:
                    viol.append(dict(k=k, seq=repr(seq), Q_eigs=th[b].round(9).tolist(), adj_edges=np.argwhere(np.triu(batch[b] - np.diag(np.diag(batch[b])), 1)).tolist()))
    res[n] = dict(m=m, graphs_with_repetition=total, max_excess=worst[0], argmax=worst[1], graphs_with_theta_near_2=near2, violations=viol[:20])
    print(n, m, total, 'max excess', worst[0], 'near2', near2, 'viol', len(viol), flush=True)
json.dump(res, open(sys.argv[4], 'w'), indent=1)
