"""Finite sanity checks for proposals/combinatorics.md.

These checks are not proofs. They test (1) the multicolour blow-up lower
construction for R(C_m; K_3, K_3), (2) the cycle-spectrum corollary of
R(C_m, K_n) on every graph with at most 7 vertices, and (3) the elementary
congruent-copy reduction on lattice point sets.

Run: python3 -I experiments/combinatorics.py
"""
import itertools
import math
import networkx as nx
from networkx.generators.atlas import graph_atlas_g


def has_cycle_of_length(G, m):
    """Exact search for a (not necessarily induced) cycle with m vertices."""
    nodes = sorted(G.nodes())
    adj = {v: set(G[v]) for v in nodes}
    for start in nodes:
        # cycles whose minimum vertex is `start`
        stack = [(start, [start])]
        while stack:
            v, path = stack.pop()
            if len(path) == m:
                if start in adj[v]:
                    return True
                continue
            for w in adj[v]:
                if w > start and w not in path:
                    stack.append((w, path + [w]))
    return False


def alpha(G):
    return max((len(c) for c in nx.find_cliques(nx.complement(G))), default=0)


def check_multicolour_blowup(m):
    # Critical 2-colouring of K_5 with no monochromatic triangle: colour 2 on
    # pentagon edges, colour 3 on pentagram edges.  R(3,3)-1 = 5 blocks.
    R = 6
    blocks = R - 1
    base = {}
    for i, j in itertools.combinations(range(blocks), 2):
        base[(i, j)] = 2 if (j - i) % 5 in (1, 4) else 3
    V = [(b, x) for b in range(blocks) for x in range(m - 1)]
    red = nx.Graph()
    red.add_nodes_from(V)
    col = {2: nx.Graph(), 3: nx.Graph()}
    for u, v in itertools.combinations(V, 2):
        if u[0] == v[0]:
            red.add_edge(u, v)
        else:
            i, j = sorted((u[0], v[0]))
            col[base[(i, j)]].add_edge(u, v)
    assert not has_cycle_of_length(red, m)  # red components have m-1 vertices
    for c in (2, 3):
        tri = sum(1 for clique in nx.find_cliques(col[c]) if len(clique) >= 3)
        assert tri == 0, (m, c)
    return len(V)


def check_cycle_spectrum(max_n=7):
    tested = 0
    for G in graph_atlas_g()[1:]:
        N = G.number_of_nodes()
        if N > max_n or N == 0:
            continue
        a = alpha(G)
        if a < 2:
            continue
        for m in range(a + 1, N + 1):
            if (m - 1) * a + 1 > N or (m, a) == (3, 2):
                continue
            tested += 1
            assert has_cycle_of_length(G, m), (nx.to_graph6_bytes(G), m)
    # sharpness: a disjoint copies of K_{m-1}
    for a, m in [(2, 4), (2, 5), (3, 4)]:
        H = nx.disjoint_union_all([nx.complete_graph(m - 1)] * a)
        assert alpha(H) == a and not has_cycle_of_length(H, m)
    return tested


def check_congruent_reduction():
    # square and triangular lattice patches; triangle T = unit equilateral
    pts_sq = [(x, y) for x in range(6) for y in range(6)]
    pts_tr = [(x + 0.5 * y, y * math.sqrt(3) / 2) for x in range(6) for y in range(6)]
    out = []
    for P in (pts_sq, pts_tr):
        d = lambda p, q: math.dist(p, q)
        u = sum(1 for p, q in itertools.combinations(P, 2) if abs(d(p, q) - 1) < 1e-9)
        tri = sum(
            1
            for p, q, r in itertools.combinations(P, 3)
            if all(abs(x - 1) < 1e-9 for x in (d(p, q), d(q, r), d(p, r)))
        )
        assert tri <= 4 * u
        out.append((len(P), u, tri))
    return out


if __name__ == "__main__":
    for m in (6, 7):
        print("multicolour blow-up verified, m =", m, "vertices =", check_multicolour_blowup(m))
    print("cycle-spectrum instances verified:", check_cycle_spectrum())
    print("congruent reduction (n, u, equilateral copies):", check_congruent_reduction())
