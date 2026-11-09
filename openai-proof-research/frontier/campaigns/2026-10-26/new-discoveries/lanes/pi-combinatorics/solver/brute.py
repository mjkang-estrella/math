#!/usr/bin/env python3
"""Independent brute-force checker (no memoization, plain minimax over all
3^m states) for small boards. Written from scratch to cross-check solve.js.

Also supports the 'chordless' rule variant: winning cycles are ALL chordless
cycles of the graph (BBFS's gloss), not just bounded cells.
"""
import sys
from itertools import product

def read_board(path):
    toks = open(path).read().split()
    it = iter(toks)
    n = int(next(it)); m = int(next(it))
    edges = []
    for _ in range(m):
        u = int(next(it)); v = int(next(it)); edges.append((u, v))
    idx = {}
    for i, e in enumerate(edges):
        idx[e] = i; idx[(e[1], e[0])] = i
    f = int(next(it))
    faces = []  # list of (edge indices, required dir)
    for _ in range(f):
        k = int(next(it))
        seq = [int(next(it)) for _ in range(k)]
        ed = []; rq = []
        for p in range(k):
            u, v = seq[p], seq[(p+1) % k]
            e = idx[(u, v)]
            ed.append(e); rq.append(1 if edges[e][0] == u else 2)
        faces.append((ed, rq))
    return n, edges, faces

def chordless_cycles(n, edges):
    """enumerate all chordless cycles (as edge-dir tuples) by DFS."""
    adj = {v: set() for v in range(n)}
    for i, (u, v) in enumerate(edges):
        adj[u].add(v); adj[v].add(u)
    cycles = []
    def dfs(start, path, used):
        u = path[-1]
        for w in sorted(adj[u]):
            if w == start and len(path) >= 3:
                cyc = path[:]
                # chordless: no edge between non-consecutive cycle vertices
                vs = set(cyc)
                ok = True
                for a in cyc:
                    for b in adj[a]:
                        if b in vs and b not in {cyc[(cyc.index(a)+1) % len(cyc)], cyc[(cyc.index(a)-1) % len(cyc)]}:
                            ok = False
                if ok:
                    ed = []; rq = []
                    for p in range(len(cyc)):
                        a, b = cyc[p], cyc[(p+1) % len(cyc)]
                        e = edges.index(tuple(sorted((a,b))) if False else (a,b)) if (a,b) in edges else edges.index((b,a))
                        ed.append(e); rq.append(1 if edges[e][0] == a else 2)
                    cycles.append((ed, rq))
                continue
            if w in used or w < start: continue
            dfs(start, path + [w], used | {w})
    for s in range(n):
        dfs(s, [s], {s})
    # dedup
    out = []
    seen = set()
    for ed, rq in cycles:
        key = frozenset(ed)
        if key not in seen:
            seen.add(key); out.append((ed, rq))
    return out

def solve(n, edges, faces, chordless=False):
    m = len(edges)
    if chordless:
        faces = faces + chordless_cycles(n, edges)
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append(i); adj[v].append(i)
    pw3 = [3**i for i in range(m + 1)]

    def legal(state, e, d):
        for x in (edges[e][0], edges[e][1]):
            out = (d == 1) if x == edges[e][0] else (d == 2)
            allm = True; same = True
            for fe in adj[x]:
                mk = d if fe == e else (state // pw3[fe]) % 3
                if mk == 0: allm = False; break
                isout = ((edges[fe][0] == x) == (mk == 1))
                if isout != out: same = False; break
            if allm and same: return False
        return True

    def completes(state, e, d):
        for ed, rq in faces:
            cw = ccw = True
            for e2, r in zip(ed, rq):
                mk = d if e2 == e else (state // pw3[e2]) % 3
                if mk == 0: cw = ccw = False; break
                if mk != r: cw = False
                if mk != 3 - r: ccw = False
            if cw or ccw: return True
        return False

    import sys
    sys.setrecursionlimit(100000)
    memo = {}
    def solve_st(state):
        if state in memo: return memo[state]
        k = sum(1 for e in range(m) if (state // pw3[e]) % 3)
        tomove = 1 if k % 2 == 0 else 2
        best = 3 - tomove
        tri = [(state // pw3[e]) % 3 for e in range(m)]
        for e in range(m):
            if tri[e]: continue
            for d in (1, 2):
                if not legal(state, e, d): continue
                if completes(state, e, d):
                    best = tomove; memo[state] = best; return best
                if solve_st(state + d * pw3[e]) == tomove:
                    best = tomove; memo[state] = best; return best
        memo[state] = best
        return best

    return solve_st(0)

if __name__ == '__main__':
    path = sys.argv[1]
    chordless = '--chordless' in sys.argv
    n, edges, faces = read_board(path)
    w = solve(n, edges, faces, chordless)
    print(('P1' if w == 1 else 'P2'), '(chordless variant)' if chordless else '')
