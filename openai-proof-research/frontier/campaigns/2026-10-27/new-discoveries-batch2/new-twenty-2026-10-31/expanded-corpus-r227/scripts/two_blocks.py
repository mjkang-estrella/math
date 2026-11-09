"""365134 structured search. Base cubic multigraph K' on 0..m-1 containing Hamilton path 0-1-...-(m-1);
t1 = a non-path edge at 0, t2 = a non-path edge at m-1 (t1 != t2). G = K' with t1 and t2 each replaced by
a 2-sum with Petersen (P10-e block). Then G has a Hamiltonian path (start in block 1, end in block 2,
provided P10-e has a Hamilton path ending at an attachment vertex, checked separately). G is bridgeless iff
K' is, and G is never 3-edge-colourable (a 2-edge-cut whose closure is P10). Report G without a
non-conflicting flow.  Usage: two_blocks.py LANE MMIN MMAX [MULTI 0/1]"""
import sys, json, pathlib, itertools
D = pathlib.Path(sys.argv[1]).resolve(); sys.path.insert(0, str(D / 'scripts'))
import ncflow as N, snarklib as L

def completions(m, multi):
    """all multisets of extra edges making path 0..m-1 cubic, loopless; canonical increasing order"""
    need = [2] + [1] * (m - 2) + [2]
    extra = []
    def rec(i):
        while i < m and need[i] == 0: i += 1
        if i == m:
            yield list(extra); return
        # vertex i needs need[i] more edges to vertices j > i (edges to j < i were already placed)
        k = need[i]
        cands = [j for j in range(i + 1, m) if need[j] > 0]
        for J in (itertools.combinations_with_replacement(cands, k) if multi else itertools.combinations(cands, k)):
            ok = True
            from collections import Counter
            cnt = Counter(J)
            for j, t in cnt.items():
                if need[j] < t: ok = False
                mult = t + (1 if j == i + 1 else 0) + extra.count((i, j))
                if mult > 2 or (not multi and mult > 1): ok = False
            if not ok: continue
            need[i] = 0
            for j in J: need[j] -= 1; extra.append((i, j))
            yield from rec(i + 1)
            for j in J: need[j] += 1; extra.pop()
            need[i] = k
    yield from rec(0)

P_n, P_E = L.petersen()
mmin, mmax = int(sys.argv[2]), int(sys.argv[3]); multi = len(sys.argv) > 4 and sys.argv[4] == '1'
stats = {}
for m in range(mmin, mmax + 1, 2):
    s = {'bases': 0, 'bridgeless_bases': 0, 'G_checked': 0, 'noflow': 0}
    for extra in completions(m, multi):
        s['bases'] += 1
        E = [(i, i + 1) for i in range(m - 1)] + extra
        if not N.bridgeless(m, E): continue
        s['bridgeless_bases'] += 1
        t1s = [k for k in range(m - 1, len(E)) if 0 in E[k]]
        t2s = [k for k in range(m - 1, len(E)) if m - 1 in E[k]]
        for k1 in t1s:
            for k2 in t2s:
                if k1 == k2: continue
                n, G = m, list(E)
                # replace k1 then k2 by 2-sums with Petersen (edge 0 of Petersen removed)
                a, b = G[k1]; c, d = G[k2]
                G = [e for j, e in enumerate(G) if j not in (k1, k2)]
                for (x, y) in ((a, b), (c, d)):
                    off = n
                    G += [(u + off, v + off) for (u, v) in P_E[1:]]
                    G += [(x, P_E[0][0] + off), (y, P_E[0][1] + off)]
                    n += 10
                inc = N.adjacency(n, G); s['G_checked'] += 1
                w = None
                for F in N.perfect_matchings(n, G, inc):
                    w = N.flow_exists(n, G, inc, F)
                    if w: break
                if not w:
                    s['noflow'] += 1
                    print('NOFLOW', json.dumps({'m': m, 'base': E, 't1': E[k1], 't2': E[k2], 'G': G}), flush=True)
    stats[m] = s
    print(json.dumps({'m': m, 'multi': multi, **s}), flush=True)
