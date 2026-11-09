#!/usr/bin/env python3
"""Strategy analysis for Theta(1,3,k) under canonical cell rules.

Extracts, for every reachable state, the winning-move set for the player to
move (when they are the overall winner), and can verify a candidate uniform
strategy by exhaustive backward simulation.

State encoding: edge i has digit (state // 3^i) % 3 in {0,1,2}.
"""
import sys
sys.setrecursionlimit(1000000)

class Board:
    def __init__(self, j, k, l, outer):
        paths = [j, k, l]
        self.paths = paths
        edges = []
        chains = []
        nxt = 2
        for L in paths:
            chain = [0] + list(range(nxt, nxt + L - 1)) + [1]
            nxt += L - 1
            chains.append(chain)
            for a, b in zip(chain, chain[1:]):
                edges.append((a, b))
        self.n = nxt
        self.edges = edges
        self.m = len(edges)
        starts = []
        s = 0
        for L in paths:
            starts.append(s)
            s += L
        self.starts = starts

        def path_edges(p):
            return list(range(starts[p], starts[p] + paths[p]))
        self.path_edges = path_edges
        self.chains = chains

        def pair_cell(pa, pb):
            cell = [(e, 1) for e in path_edges(pa)] + [(e, 2) for e in path_edges(pb)]
            return cell

        pairs = [(0, 1), (1, 2), (0, 2)]
        self.cells = [pair_cell(a, b) for (a, b) in pairs if (a, b) != pairs[outer]]
        self.outer = outer

        self.cell_of_edge = [[] for _ in range(self.m)]
        for ci, cell in enumerate(self.cells):
            for (e, r) in cell:
                self.cell_of_edge[e].append(ci)

        self.inc = [[] for _ in range(self.n)]
        for i, (u, v) in enumerate(edges):
            self.inc[u].append(i)
            self.inc[v].append(i)

        self.pw3 = [3 ** i for i in range(self.m + 1)]
        self.memo = {}

    # ---- state helpers ----
    def digits(self, state):
        t = state
        res = []
        for _ in range(self.m):
            res.append(t % 3)
            t //= 3
        return res

    def marked_count(self, state):
        return sum(1 for d in self.digits(state) if d)

    def player(self, state):
        return 1 if self.marked_count(state) % 2 == 0 else 2

    def move_effects(self, state, e, d):
        """None illegal; 'win' completes a cell; 'ok' legal non-winning."""
        edges = self.edges
        tri = self.digits(state)
        tri[e] = d
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
        for ci in self.cell_of_edge[e]:
            cw = ccw = True
            for (e2, r) in self.cells[ci]:
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

    def legal_moves(self, state):
        tri = self.digits(state)
        res = []
        for e in range(self.m):
            if tri[e]:
                continue
            for d in (1, 2):
                if self.move_effects(state, e, d):
                    res.append((e, d))
        return res

    def solve(self, state=0):
        memo = self.memo
        v = memo.get(state)
        if v is not None:
            return v
        tomove = self.player(state)
        best = 3 - tomove
        tri = self.digits(state)
        for e in range(self.m):
            if tri[e]:
                continue
            for d in (1, 2):
                eff = self.move_effects(state, e, d)
                if eff is None:
                    continue
                if eff == 'win':
                    memo[state] = tomove
                    return tomove
                if self.solve(state + d * self.pw3[e]) == tomove:
                    memo[state] = tomove
                    return tomove
        memo[state] = best
        return best

    def reachable(self):
        """All states reachable from empty via legal play (stopping at wins)."""
        seen = {0}
        stack = [0]
        while stack:
            st = stack.pop()
            tri = self.digits(st)
            for e in range(self.m):
                if tri[e]:
                    continue
                for d in (1, 2):
                    eff = self.move_effects(st, e, d)
                    if eff is None:
                        continue
                    ns = st + d * self.pw3[e]
                    if eff == 'ok' and ns not in seen:
                        seen.add(ns)
                        stack.append(ns)
        return seen

    # ---- candidate strategy verification ----
    def verify_strategy(self, strat, winner, max_nodes=10**9):
        """strat: function(state, board) -> (e,d) or None. The `winner` follows
        strat at their turns; opponent plays ALL legal moves (exhaustive AND-node
        expansion). Returns (True, stats) if winner wins every play."""
        # opponent = 3 - winner
        # DFS over states; at winner's turn apply strat (must be legal);
        # at opponent's turn branch over all legal moves.
        stats = {'nodes': 0, 'wins_by_cell': 0, 'wins_by_last': 0}
        import sys
        seen = set()

        def rec(state):
            stats['nodes'] += 1
            if stats['nodes'] > max_nodes:
                raise RuntimeError('node limit')
            p = self.player(state)
            tri = self.digits(state)
            moves = []
            for e in range(self.m):
                if tri[e]:
                    continue
                for d in (1, 2):
                    eff = self.move_effects(state, e, d)
                    if eff:
                        moves.append((e, d, eff))
            if not moves:
                # terminal: last mover wins
                last = 3 - p
                if last == winner:
                    stats['wins_by_last'] += 1
                    return True
                return False
            if p == winner:
                mv = strat(state, self)
                if mv is None:
                    return False
                e, d = mv
                eff = self.move_effects(state, e, d)
                if eff is None:
                    return False
                if eff == 'win':
                    stats['wins_by_cell'] += 1
                    return True
                return rec(state + d * self.pw3[e])
            else:
                for (e, d, eff) in moves:
                    if eff == 'win':
                        return False  # opponent completes a cell
                    if not rec(state + d * self.pw3[e]):
                        return False
                return True

        ok = rec(0)
        return ok, stats

    def state_str(self, state):
        names = self.edge_names()
        tri = self.digits(state)
        return ' '.join(f"{names[i]}{'.' if tri[i]==0 else ('F' if tri[i]==1 else 'B')}" for i in range(self.m))

    def edge_names(self):
        names = []
        for idx, L in enumerate(self.paths):
            for i in range(L):
                names.append(f"P{idx}[{i}]")
        return names

def fmt_dir(d):
    return '.' if d == 0 else ('F' if d == 1 else 'B')

if __name__ == '__main__':
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    for outer in range(3):
        b = Board(1, 3, k, outer)
        w = b.solve(0)
        m = b.m
        print(f"Theta(1,3,{k}) outer={outer} (paths A=1,B=3,C={k}): m={m} parity pred P{1 if m%2 else 2}, winner P{w}, states={len(b.memo)}")
