"""
Brute-force solver for the Game of Arrows (Game of Cycles on a tree).

Direct implementation of the rules on the ORIGINAL tree, no decomposition:
  * a position is an assignment of each edge to {unmarked, u->v, v->u};
  * a move marks one unmarked edge with a direction;
  * a move is illegal if afterwards some vertex of degree >= 1 has all of its
    incident edges marked and all pointing in (sink) or all pointing out (source);
  * normal play: the player who cannot move loses.

Returns Grundy values by memoized recursion over full edge-state tuples.
Exponential (3^m states) -- used only as an independent check on small trees.
"""
from functools import lru_cache
import sys

sys.setrecursionlimit(100000)


def grundy_tree(n, edges):
    """n vertices 0..n-1, edges list of (u,v). Returns Grundy value of the empty board."""
    m = len(edges)
    inc = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        inc[u].append(i)
        inc[v].append(i)

    def bad_vertex(state, w):
        # state[i]: 0 unmarked, 1 means edges[i][0]->edges[i][1], 2 means reverse
        if not inc[w]:
            return False
        all_in = True
        all_out = True
        for i in inc[w]:
            s = state[i]
            if s == 0:
                return False
            u, v = edges[i]
            head = v if s == 1 else u
            if head == w:
                all_out = False
            else:
                all_in = False
        return all_in or all_out

    @lru_cache(maxsize=None)
    def g(state):
        opts = set()
        st = list(state)
        for i in range(m):
            if st[i] != 0:
                continue
            for d in (1, 2):
                st[i] = d
                u, v = edges[i]
                if not bad_vertex(st, u) and not bad_vertex(st, v):
                    opts.add(g(tuple(st)))
                st[i] = 0
        x = 0
        while x in opts:
            x += 1
        return x

    return g(tuple([0] * m))


def spider_edges(legs):
    """Spider with given leg lengths (number of edges per leg, original tree)."""
    edges = []
    nxt = 1
    for L in legs:
        prev = 0
        for _ in range(L):
            edges.append((prev, nxt))
            prev = nxt
            nxt += 1
    return nxt, edges


if __name__ == "__main__":
    legs = tuple(int(a) for a in sys.argv[1:])
    n, e = spider_edges(legs)
    print(legs, "markable =", sum(legs) - len(legs), "grundy =", grundy_tree(n, e))
