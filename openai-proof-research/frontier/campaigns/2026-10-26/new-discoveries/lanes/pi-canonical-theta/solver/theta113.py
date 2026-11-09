#!/usr/bin/env python3
"""Theta board generator + exact solver with strategy extraction (canonical cell rule).

Board = simple connected plane graph + its bounded cells (AMM 2021 rules).
State: each edge in {0 unmarked, 1 forward, 2 backward} w.r.t. a fixed reference
orientation of each edge. Move: mark an unmarked edge in a direction that creates
no sink/source. Win: move completes a bounded cell (all edges marked, cyclically
consistent). Else the player making the last legal move wins.

Theta(j,k,l) with u=0,v=1 and three internally disjoint paths of lengths j,k,l.
The plane embeddings of a theta graph correspond to which path-pair bounds the
outer face; the other two path-pair cycles are the bounded cells.
"""
import sys
from functools import lru_cache
sys.setrecursionlimit(1000000)

# ---------- board representation ----------
# edges: list of (u,v) reference direction
# cells: list of list of (edge_idx, req_dir) meaning: cell completed when every
# edge marked and all marked == req_dir (one cyclic direction) or all == 3-req_dir.

def theta_cells(j, k, l):
    """Return (n, edges, cells) for Theta(j,k,l), cells for each embedding choice.
    paths: P0 length j, P1 length k, P2 length l. Path i: 0 = v0_1 = ... = v1.
    Embedding with outer face = pair (a,b) => bounded cells are the other two pairs.
    Returns list of (edges, cells) one per outer choice (0,1,2).
    """
    paths = [j, k, l]
    edges = []
    chains = []
    nxt = 2
    for L in paths:
        chain = [0] + list(range(nxt, nxt + L - 1)) + [1]
        nxt += L - 1
        chains.append(chain)
        for a, b in zip(chain, chain[1:]):
            edges.append((a, b))
    n = nxt - 1 + 1  # last vertex id used +1
    # path p occupies edge indices: start sums
    starts = []
    s = 0
    for L in paths:
        starts.append(s)
        s += L
    def path_edges(p):
        return list(range(starts[p], starts[p] + paths[p]))

    def pair_cell(pa, pb):
        """Cycle: 0 ->(path pa)-> 1 ->(path pb reversed)-> 0.
        Consistent direction: pa forward (0->1), pb backward, or pa backward,
        pb forward. Reference directions: edges stored along each chain 0->...->1,
        so 'forward' = req dir 1 for pa edges (u->v as stored (a,b) with a earlier).
        Wait: edges stored as (chain[i], chain[i+1]) i.e. along path direction 0->1.
        req dir 1 means marked as (u->v) i.e. forward. For the cycle 0->1 via pa
        then 1->0 via pb: pa forward (1), pb edges need direction 1->0 = backward (2)
        as stored. So cell complete iff (all pa ==1 and all pb ==2) or (all pa==2
        and all pb==1)."""
        cell = []
        for e in path_edges(pa):
            cell.append((e, 1))
        for e in path_edges(pb):
            cell.append((e, 2))
        return cell

    boards = []
    pairs = [(0, 1), (1, 2), (0, 2)]
    for outer in range(3):
        cells = []
        for (a, b) in pairs:
            if (a, b) == pairs[outer]:
                continue
            cells.append(pair_cell(a, b) if False else None)
        # pair_cell returns list with pa fwd/pb bwd encoding; cyclic consistency
        # means completed iff all marked and (all==req) or (all==3-req). That is
        # handled by the checker. But the cell (pa,pb) with pa fwd pb bwd: req list
        # as built: pa:1, pb:2 -> "all == req" is the pa-fwd orientation. Good.
        cells = []
        for (a, b) in pairs:
            if (a, b) == pairs[outer]:
                continue
            cells.append(pair_cell(a, b))
        boards.append((edges, cells))
    return n, boards

# ---------- solver ----------
class Solver:
    def __init__(self, n, edges, cells):
        self.n = n
        self.edges = edges
        self.m = len(edges)
        self.cells = cells
        self.inc = [[] for _ in range(n)]
        for i, (u, v) in enumerate(edges):
            self.inc[u].append(i)
            self.inc[v].append(i)
        # precompute cell -> edge list with req dirs
        self.cells = cells
        self.memo = {}
        self.pw3 = [3 ** i for i in range(self.m + 1)]

    def legal_and_effect(self, state, e, d):
        """Return 'win' if move completes a cell, 'ok' if legal non-winning,
        None if illegal."""
        edges = self.edges
        m = self.m
        tri = [(state // self.pw3[i]) % 3 for i in range(m)]
        tri[e] = d
        # sink/source check at both endpoints
        for x in (edges[e][0], edges[e][1]):
            out = (d == 1) if edges[e][0] == x else (d == 2)
            allm = True
            same = True
            for fe in self.inc[x]:
                mk = tri[fe]
                if mk == 0:
                    allm = False
                    break
                isout = ((edges[fe][0] == x) == (mk == 1))
                if isout != out:
                    same = False
                    break
            if allm and same:
                return None
        # cell completion check: only cells containing e matter
        for cell in self.cells:
            contains = False
            for (e2, r) in cell:
                if e2 == e:
                    contains = True
                    break
            if not contains:
                continue
            cw = True
            ccw = True
            for (e2, r) in cell:
                mk = tri[e2]
                if mk == 0:
                    cw = ccw = False
                    break
                if mk != r:
                    cw = False
                if mk != 3 - r:
                    ccw = False
            if cw or ccw:
                return 'win'
        return 'ok'

    def solve(self, state=0):
        memo = self.memo
        v = memo.get(state)
        if v is not None:
            return v
        m = self.m
        cnt = 0
        t = state
        for i in range(m):
            if t % 3:
                cnt += 1
            t //= 3
        tomove = 1 if cnt % 2 == 0 else 2
        best = 3 - tomove
        t = state
        tris = [(state // self.pw3[i]) % 3 for i in range(m)]
        for e in range(m):
            if tris[e]:
                continue
            for d in (1, 2):
                eff = self.legal_and_effect(state, e, d)
                if eff is None:
                    continue
                if eff == 'win':
                    best = tomove
                    memo[state] = best
                    return best
                if self.solve(state + d * self.pw3[e]) == tomove:
                    best = tomove
                    memo[state] = best
                    return best
        memo[state] = best
        return best

    def winning_moves(self, state):
        """All moves (e,d) that are winning for the player to move, from a state
        where the player to move is the overall winner."""
        w = self.solve(state)
        m = self.m
        cnt = bin_count(state, m)
        tomove = 1 if cnt % 2 == 0 else 2
        if w != tomove:
            return None
        res = []
        tris = [(state // self.pw3[i]) % 3 for i in range(m)]
        for e in range(m):
            if tris[e]:
                continue
            for d in (1, 2):
                eff = self.legal_and_effect(state, e, d)
                if eff == 'win':
                    res.append((e, d, 'win'))
                elif eff == 'ok' and self.solve(state + d * self.pw3[e]) == tomove:
                    res.append((e, d, 'cont'))
        return res

def bin_count(state, m):
    c = 0
    for i in range(m):
        c += 1 if (state % 3) else 0
        state //= 3
    return c

def fmt_state(state, m, names):
    s = []
    for i in range(m):
        v = (state // 3**i) % 3
        s.append('.' if v == 0 else ('F' if v == 1 else 'B'))
    return ' '.join(f"{names[i]}={s[i]}" for i in range(m))

def theta_edge_names(j, k, l):
    names = []
    for idx, L in enumerate([j, k, l]):
        for i in range(L):
            names.append(f"P{idx}[{i}]")
    return names

if __name__ == '__main__':
    j, k, l = 1, 3, int(sys.argv[1]) if len(sys.argv) > 1 else 5
    n, boards = theta_cells(j, k, l)
    names = theta_edge_names(j, k, l)
    m = len(boards[0][0])
    print(f"Theta({j},{k},{l}): m={m} edges, parity predicts {'P1' if m%2 else 'P2'}")
    for outer, (edges, cells) in enumerate(boards):
        s = Solver(n, edges, cells)
        w = s.solve(0)
        print(f"outer={outer}: winner P{w}  [{len(s.memo)} states]")
        wm = s.winning_moves(0)
        print("  initial winning moves:", [(names[e], 'F' if d==1 else 'B', t) for e,d,t in wm])
