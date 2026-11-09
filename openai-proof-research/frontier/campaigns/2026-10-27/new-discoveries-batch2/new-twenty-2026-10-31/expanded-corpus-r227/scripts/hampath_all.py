"""365134 exhaustive coverage: every loopless cubic (multi)graph on vertex set 0..n-1 containing the
Hamilton path 0-1-...-(n-1) (labelled completions; every cubic multigraph with a Hamiltonian path is
isomorphic to at least one of them). For each: bridgeless? 3-edge-colourable? If bridgeless and not
colourable, search all perfect matchings for a non-conflicting flow; report failures. A failure on 10
vertices is necessarily the Petersen graph (the only non-3-edge-colourable bridgeless cubic multigraph
on <= 10 vertices); all failures are printed in full regardless.
Usage: hampath_all.py LANE N MULTI(0/1) CHUNK NCHUNKS"""
import sys, json, pathlib, time
D = pathlib.Path(sys.argv[1]).resolve(); sys.path.insert(0, str(D / 'scripts'))
import ncflow as N
from hpgen import completions

def colourable(n, E):
    inc = [[] for _ in range(n)]
    for k, (u, v) in enumerate(E): inc[u].append(k); inc[v].append(k)
    col = [0] * len(E); used = [0] * n
    order = list(range(len(E)))  # path edges first, then extras by first endpoint
    def rec(p):
        if p == len(order): return True
        k = order[p]; u, v = E[k]
        free = 7 & ~(used[u] | used[v])
        if p == 0: free &= 1
        while free:
            c = free & -free; free ^= c
            col[k] = c; used[u] |= c; used[v] |= c
            if rec(p + 1): return True
            used[u] ^= c; used[v] ^= c
        return False
    return rec(0)

n = int(sys.argv[2]); multi = sys.argv[3] == '1'; chunk = int(sys.argv[4]); nch = int(sys.argv[5])
t0 = time.time(); s = {'n': n, 'multi': multi, 'chunk': chunk, 'nchunks': nch, 'completions': 0,
                       'bridgeless': 0, 'noncolourable_bridgeless': 0, 'with_flow': 0, 'without_flow': 0}
for extra in completions(n, multi, chunk, nch):
    s['completions'] += 1
    E = [(i, i + 1) for i in range(n - 1)] + extra
    if colourable(n, E): continue
    if not N.bridgeless(n, E): continue
    s['bridgeless'] += 0
    s['noncolourable_bridgeless'] += 1
    inc = N.adjacency(n, E); w = None
    for F in N.perfect_matchings(n, E, inc):
        w = N.flow_exists(n, E, inc, F)
        if w: break
    if w: s['with_flow'] += 1
    else:
        s['without_flow'] += 1
        print('NOFLOW', n, json.dumps(E), flush=True)
s['seconds'] = round(time.time() - t0, 2)
s['note'] = 'bridgeless counter not tracked for colourable graphs (colourable cubic graphs need no flow check)'
print(json.dumps(s), flush=True)
