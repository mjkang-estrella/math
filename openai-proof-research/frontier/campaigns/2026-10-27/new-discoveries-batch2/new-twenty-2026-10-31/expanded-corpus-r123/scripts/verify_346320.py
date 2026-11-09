# 346320: independent exact (Fraction) re-implementation of Algorithm S1S2 of arXiv:2004.14574v4
# (Appendix A.1) with SHRINK/UPDATE's graph part (15),(16).  The unspecified choices of the
# pseudocode ("Select a vertex u in H", order of "for v in N(u)") are supplied explicitly.
# Two runs on the same input end with shrunk support graphs of 3 and 4 vertices.
from fractions import Fraction as F
import itertools, json, sys

h = F(1, 2)
y = {0: h, 1: F(1), 2: F(1), 3: F(1), 4: F(1), 5: F(1)}
E = {(0, 4): h, (0, 5): h, (1, 2): F(1), (1, 3): F(1), (2, 3): h, (2, 5): h, (3, 4): h, (4, 5): F(1)}

def check_PA(y, x):
    V = list(y)
    for v in V:
        assert sum(x.get(frozenset((u, v)), 0) for u in V if u != v) == 2 * y[v]   # (7a)
        assert 0 <= y[v] <= 1                                                     # (7e)
    for e, val in x.items():
        assert val >= 0 and all(val <= y[v] for v in e)                          # (7f),(7b)
    return True

def shrink(G, S, name):
    # G = (y, x, members); S = frozenset of two current vertices
    y, x, mem = G
    y2 = {v: y[v] for v in y if v not in S}
    x2 = {}
    for e, val in x.items():
        e2 = frozenset(name if v in S else v for v in e)
        if len(e2) == 2: x2[e2] = x2.get(e2, 0) + val
    x2 = {e: v for e, v in x2.items() if v > 0}                   # support graph (15b)
    y2[name] = sum(v for e, v in x.items() if len(e & S) == 1) / 2   # (16d)
    mem2 = {v: mem[v] for v in mem if v not in S}; mem2[name] = frozenset().union(*(mem[v] for v in S))
    return (y2, x2, mem2)

def N(G, u):
    return [v for v in G[0] if v != u and frozenset((u, v)) in G[1]]

def s1s2(G, select_order, nbr_order, log):
    """Literal Algorithm S1S2.  select_order(H, G) picks u in H; nbr_order(u, G) orders N(u)."""
    H = set(G[0]); fresh = itertools.count(100)
    while H:
        u = select_order(H, G); H.discard(u); c = G[0][u]
        for v in nbr_order(u, G):
            xuv = G[1][frozenset((u, v))]
            if G[0][v] == c and xuv == c:
                if any(G[0][w] >= c for w in G[0] if w not in (u, v)):
                    s = next(fresh); log.append(('S1', sorted(G[2][u]), sorted(G[2][v]), str(c)))
                    G = shrink(G, frozenset((u, v)), s)
                    H = {s if z in (u, v) else z for z in H} | {s} | set(N(G, s)); H.discard(u); H.discard(v)
                    break
            elif xuv > G[0][u] and xuv > G[0][v]:
                s = next(fresh); log.append(('S2', sorted(G[2][u]), sorted(G[2][v]), str(xuv)))
                G = shrink(G, frozenset((u, v)), s)
                H = {s if z in (u, v) else z for z in H} | {s} | set(N(G, s)); H.discard(u); H.discard(v)
                break
    return G

def run(priority):
    # priority: list of original-vertex preferences; merged vertices are ranked by their
    # smallest preferred member; neighbours scanned in the same preference order.
    x = {frozenset(e): v for e, v in E.items()}
    G = (dict(y), x, {v: frozenset([v]) for v in y})
    rank = lambda G, z: min(priority.index(m) for m in G[2][z])
    sel = lambda H, G: min(H, key=lambda z: rank(G, z))
    nb = lambda u, G: sorted(N(G, u), key=lambda z: rank(G, z))
    log = []
    G = s1s2(G, sel, nb, log)
    blocks = sorted(sorted(G[2][v]) for v in G[0])
    return {'log': log, 'final_blocks': blocks, 'final_y': {str(sorted(G[2][v])): str(G[0][v]) for v in G[0]},
            'final_x': {str(sorted(sorted(G[2][v]) for v in e)): str(val) for e, val in G[1].items()},
            'num_vertices': len(G[0]), 'num_edges': len(G[1])}

if __name__ == '__main__':
    assert check_PA(y, {frozenset(e): v for e, v in E.items()})
    rA = run([4, 5, 1, 2, 3, 0])   # first shrink {4,5}
    rB = run([1, 2, 3, 0, 4, 5])   # first shrink {1,2}
    out = {'input_y': {k: str(v) for k, v in y.items()}, 'input_x': {str(k): str(v) for k, v in E.items()},
           'in_PA': True, 'runA': rA, 'runB': rB,
           'nonisomorphic_reason': 'different numbers of vertices' if rA['num_vertices'] != rB['num_vertices'] else None}
    print(json.dumps(out, indent=1))
    assert rA['num_vertices'] == 3 and rB['num_vertices'] == 4
