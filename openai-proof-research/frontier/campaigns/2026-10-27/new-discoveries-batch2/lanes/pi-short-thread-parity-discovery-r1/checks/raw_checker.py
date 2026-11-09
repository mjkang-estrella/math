"""
Fully independent raw-rules checker: the Game of Arrows on an actual tree,
with positions as assignments in {0,+1,-1}^E (0 = unmarked, +1 = oriented
u->v, -1 = v->u) and the LITERAL sink/source legality of Section 2.2 of
arXiv:2610.15145v1:

  a vertex v is a sink  if v has at least one edge, all edges at v are
  marked, and all of them point into v;  a source if all point away.

  orienting unmarked edge uv as u->v is legal iff afterwards neither u nor v
  is a sink or a source.  The player making the last legal move wins.

No result of the paper is used anywhere in this file.  Used only to
cross-validate the fast solver on small instances and to certify witnesses.
"""
import sys
sys.setrecursionlimit(1000000)


def raw_g(n, edges, pos=None, memo=None):
    """Grundy value of the position `pos` on the tree (n, edges)."""
    if memo is None:
        memo = {}
    if pos is None:
        pos = (0,) * len(edges)
    key = pos
    v = memo.get(key)
    if v is not None:
        return v
    inc = [[] for _ in range(n)]
    for i, (u, w) in enumerate(edges):
        inc[u].append(i)
        inc[w].append(i)

    def makes_sink_or_source(x, i, d):
        """After orienting edge i in direction d, is x a sink or source?"""
        dirs = set()
        for j in inc[x]:
            p = d if j == i else pos[j]
            if p == 0:
                return False  # x keeps an unmarked edge
            a, b = edges[j]
            # p=+1: arc a->b ; p=-1: arc b->a
            out = (x == a and p == 1) or (x == b and p == -1)
            dirs.add('out' if out else 'in')
        # all edges at x are marked; sink/source iff all arcs agree
        return len(dirs) == 1

    opts = set()
    for i in range(len(edges)):
        if pos[i] != 0:
            continue
        u, w = edges[i]
        for d in (1, -1):
            if makes_sink_or_source(u, i, d) or makes_sink_or_source(w, i, d):
                continue
            npos = pos[:i] + (d,) + pos[i + 1:]
            opts.add(raw_g(n, edges, npos, memo))
    val = 0
    while val in opts:
        val += 1
    memo[key] = val
    return val
