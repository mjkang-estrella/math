"""Independent brute-force Grundy solver for status-labelled forests, using only the
legality rule of Lemma 3.2 (no normal form, no canonical forms). Memo on the full state."""
from functools import lru_cache
import sys

def mulO(s): return 'f' if s in 'if' else 'o'
def mulI(s): return 'f' if s in 'of' else 'i'

def grundy(statuses, edges):
    statuses = tuple(statuses)
    edges = frozenset(tuple(e) for e in edges)
    @lru_cache(maxsize=None)
    def g(st, E):
        d = {}
        for (u, v) in E:
            d[u] = d.get(u, 0) + 1; d[v] = d.get(v, 0) + 1
        opts = set()
        for (a, b) in E:
            for (u, v) in ((a, b), (b, a)):
                if (d[u] >= 2 or st[u] in 'if') and (d[v] >= 2 or st[v] in 'of'):
                    s2 = list(st); s2[u] = mulO(st[u]); s2[v] = mulI(st[v])
                    opts.add(g(tuple(s2), E - {(a, b)}))
        m = 0
        while m in opts: m += 1
        return m
    return g(statuses, edges)

def raw_tree_grundy(n, E):
    """Raw rules on the actual tree: position = orientation/unmarked per edge; a move is legal
    iff afterwards neither endpoint is a sink or source (vertex with >=1 edge, all marked, all in / all out)."""
    adj = [[] for _ in range(n)]
    for k, (u, v) in enumerate(E):
        adj[u].append(k); adj[v].append(k)
    @lru_cache(maxsize=None)
    def g(pos):
        opts = set()
        for k in range(len(E)):
            if pos[k] != 0: continue
            for o in (1, 2):  # 1: E[k][0]->E[k][1], 2: reverse
                p2 = list(pos); p2[k] = o; p2 = tuple(p2)
                ok = True
                for x in E[k]:
                    ins = outs = unm = 0
                    for j in adj[x]:
                        if p2[j] == 0: unm += 1
                        else:
                            head = E[j][1] if p2[j] == 1 else E[j][0]
                            if head == x: ins += 1
                            else: outs += 1
                    if unm == 0 and (ins == 0 or outs == 0): ok = False
                if ok: opts.add(g(p2))
        m = 0
        while m in opts: m += 1
        return m
    return g(tuple([0] * len(E)))
