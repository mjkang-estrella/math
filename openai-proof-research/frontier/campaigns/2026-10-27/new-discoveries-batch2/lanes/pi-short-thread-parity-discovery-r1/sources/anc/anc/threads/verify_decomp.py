"""Independent verification with the paper's normal-form solver ../core/decomp.py (P2):
convert a piece 'P n edges' into a tree T by attaching a pendant leaf to every leaf of the piece,
then compute g(T) and m(T) with decomp.grundy_original_tree."""
import sys, time
sys.path.insert(0, '../core')
import decomp
for line in sys.stdin:
    t = line.split()
    if not t or 'P' not in t: continue
    t = t[t.index('P'):]
    n = int(t[1]); E = [(int(t[2 + 2 * i]), int(t[3 + 2 * i])) for i in range(n - 1)]
    deg = [0] * n
    for u, v in E: deg[u] += 1; deg[v] += 1
    TE = list(E); nn = n
    for v in range(n):
        if deg[v] == 1:
            TE.append((v, nn)); nn += 1
    d2 = [0] * nn
    for u, v in TE: d2[u] += 1; d2[v] += 1
    m = sum(1 for u, v in TE if d2[u] > 1 and d2[v] > 1)
    t0 = time.time()
    g = decomp.grundy_original_tree(nn, TE)
    print("tree vertices=%d m=%d g=%d (%.1fs) edges=%s" % (nn, m, g, time.time() - t0, " ".join("%d-%d" % e for e in TE)), flush=True)
