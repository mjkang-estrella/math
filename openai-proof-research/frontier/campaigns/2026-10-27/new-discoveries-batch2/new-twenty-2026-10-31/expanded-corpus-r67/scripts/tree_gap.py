# Diagnostic for MathDB 372569: among all trees on n vertices, is lambda1-lambda2 minimised by DC(k,k,l), 2k+l=n?
# Uses NetworkX nonisomorphic_trees (vendored copy from r65) and numpy eigvalsh.  Floating point: diagnostic only.
import sys, json, pathlib, numpy as np
import networkx as nx
D = pathlib.Path(__file__).resolve().parents[1]
def gap(T):
    A = nx.to_numpy_array(T); w = np.linalg.eigvalsh(A); return w[-1] - w[-2]
def dc(k1, k2, l):
    T = nx.path_graph(l); m = l
    for _ in range(k1): T.add_edge(0, m); m += 1
    for _ in range(k2): T.add_edge(l - 1, m); m += 1
    return T
res = {}
for n in range(4, int(sys.argv[1]) + 1):
    best = []; cnt = 0
    for T in nx.nonisomorphic_trees(n):
        cnt += 1; g = gap(T); best.append((g, sorted(d for _, d in T.degree())))
        best.sort(key=lambda x: x[0]); best = best[:3]
    dcs = {}
    for l in range(1, n + 1):
        if (n - l) % 2 == 0 and (n - l) // 2 >= 1:
            k = (n - l) // 2; dcs[f'DC({k},{k},{l})'] = gap(dc(k, k, l))
    mdc = min(dcs.values()); bestdc = min(dcs, key=dcs.get)
    res[n] = dict(trees=cnt, min_gap=best[0][0], min_degseq=best[0][1], second=best[1][0] if len(best) > 1 else None, best_DC=bestdc, best_DC_gap=float(mdc), DC_attains=bool(abs(mdc - best[0][0]) < 1e-9))
    print(n, res[n], flush=True)
(D / 'outputs/tree_gap.json').write_text(json.dumps(res, indent=1, default=lambda o: o.item()) + '\n')
