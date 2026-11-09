"""365134 structured search beyond the source's Theorem 4. Base cubic multigraph K' with Hamilton path
0..m-1. Ends are replaced by Petersen blocks: 'v' = vertex replaced by P10-v (3-sum), 'e' = a non-path
edge at the end replaced by P10-e (2-sum). Modes: vv, ve (vertex 0 -> P10-v, edge at m-1 -> P10-e).
P10-v has a Hamiltonian cycle (P10 hypohamiltonian), P10-e has a Hamilton path ending at either
attachment vertex (checked in run log), so G has a Hamiltonian path. Every such G is non-3-edge-
colourable (small cut whose side closes to P10) and every 2-factor has >= 3 cycles.
Usage: end_blocks.py LANE MODE MMIN MMAX"""
import sys, json, pathlib
D = pathlib.Path(sys.argv[1]).resolve(); sys.path.insert(0, str(D / 'scripts'))
import ncflow as N, snarklib as L
from hpgen import completions
P_n, P_E = L.petersen()

def vertex_block(n, E, u):
    """replace vertex u (degree 3) by P10 - 0; attachments are the Petersen neighbours of 0: 1, 4, 5"""
    off = n
    G = []; att = [1 + off, 4 + off, 5 + off]; c = 0
    for (a, b) in E:
        if a == u: G.append((att[c], b)); c += 1
        elif b == u: G.append((a, att[c])); c += 1
        else: G.append((a, b))
    G += [(a + off, b + off) for (a, b) in P_E if 0 not in (a, b)]
    return G

def edge_block(n, E, k):
    a, b = E[k]; off = n
    G = [e for j, e in enumerate(E) if j != k]
    G += [(u + off, v + off) for (u, v) in P_E[1:]]
    G += [(a, P_E[0][0] + off), (b, P_E[0][1] + off)]
    return G

def relabel(E):
    vs = sorted({x for e in E for x in e}); mp = {v: i for i, v in enumerate(vs)}
    return len(vs), [(mp[a], mp[b]) for a, b in E]

mode = sys.argv[2]; mmin, mmax = int(sys.argv[3]), int(sys.argv[4])
for m in range(mmin, mmax + 1, 2):
    s = {'mode': mode, 'm': m, 'bases': 0, 'G_checked': 0, 'noflow': 0}
    for extra in completions(m, True):
        E = [(i, i + 1) for i in range(m - 1)] + extra
        if not N.bridgeless(m, E): continue
        s['bases'] += 1
        variants = []
        if mode == 'vv':
            G = vertex_block(m, E, 0); G = vertex_block(m + 10, G, m - 1); variants.append(G)
        elif mode == 've':
            G0 = vertex_block(m, E, 0)
            for k in range(len(G0)):
                if (m - 1) in G0[k] and G0[k] != (m - 2, m - 1):
                    variants.append(edge_block(m + 10, G0, k))
        for G in variants:
            n, G = relabel(G)
            inc = N.adjacency(n, G); s['G_checked'] += 1; w = None
            for F in N.perfect_matchings(n, G, inc):
                w = N.flow_exists(n, G, inc, F)
                if w: break
            if not w:
                s['noflow'] += 1; print('NOFLOW', json.dumps({'m': m, 'base': E, 'G': G}), flush=True)
    print(json.dumps(s), flush=True)
