"""Armbruster-Di-Hanson-Shank Conjecture componentconjecture (arXiv:2106.16242 v2; MathDB 351162), exhaustive for
labelled graphs on n vertices: r = 1/k, n multiple of k.  CO_e^{1/k}(G) = min over partitions of V into blocks of size
<= n/k of the number of crossing edges (removing the crossing edges of an optimal partition is a minimum edge
disconnecting set; conversely the components of any failure state refine such a partition).  For each m, among the
maximisers G of CO_e over G(n,m), test whether some G has a minimum disconnecting set E' whose failure state G-E' has
exactly k components, each of order n/k.  usage: propconn.py n k"""
import sys, itertools, json
n, k = int(sys.argv[1]), int(sys.argv[2]); s = n // k
E = list(itertools.combinations(range(n), 2)); idx = {e: i for i, e in enumerate(E)}
def partitions(elems):
    if not elems: yield []; return
    f, rest = elems[0], elems[1:]
    for sub in partitions(rest):
        for i in range(len(sub)): yield sub[:i] + [[f] + sub[i]] + sub[i + 1:]
        yield [[f]] + sub
parts = [p for p in partitions(list(range(n))) if max(len(b) for b in p) <= s]
info = []
for p in parts:
    blk = {v: i for i, b in enumerate(p) for v in b}
    cross = sum(1 << idx[e] for e in E if blk[e[0]] != blk[e[1]])
    info.append((cross, p))
def connected(vs, g):
    vs = list(vs); seen = {vs[0]}; st = [vs[0]]
    while st:
        x = st.pop()
        for y in vs:
            if y not in seen and (g >> idx[tuple(sorted((x, y)))]) & 1: seen.add(y); st.append(y)
    return len(seen) == len(vs)
best = {}
for g in range(1 << len(E)):
    m = bin(g).count('1')
    co = min(bin(g & c).count('1') for c, _ in info)
    b = best.get(m)
    if b is None or co > b[0]: best[m] = [co, 0, 0, None]
    if best[m][0] == co:
        best[m][1] += 1
        good = any(bin(g & c).count('1') == co and len(p) == k and all(len(B) == s for B in p) and all(connected(B, g) for B in p)
                   for c, p in info)
        if good: best[m][2] += 1
        elif best[m][3] is None: best[m][3] = [e for i, e in enumerate(E) if (g >> i) & 1]
out = {m: dict(max_CO=v[0], maximisers=v[1], maximisers_with_equal_component_failure_state=v[2], example_bad=v[3] if v[2] == 0 else None) for m, v in sorted(best.items())}
fails = [m for m, v in out.items() if v['maximisers_with_equal_component_failure_state'] == 0]
print(json.dumps(dict(n=n, k=k, failing_m=fails, by_m=out)))
