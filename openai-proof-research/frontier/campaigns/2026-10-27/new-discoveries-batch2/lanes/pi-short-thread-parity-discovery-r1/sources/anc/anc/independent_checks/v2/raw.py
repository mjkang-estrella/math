"""Raw-rules brute force for the Game of Arrows on a tree (Section 2 rules only),
plus an exhaustive check that every reachable position of a small spider has
raw Grundy value = Gamma(state) xor (detached runs) as described in Section 6.
"""
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
import spider as SP


def build_spider(xs):
    # vertex 0 = centre. leg t: vertices v_1..v_{x+1}; edge e_m = (v_{m-1}, v_m), e_{x+1} pendant
    edges = []
    legs = []
    nv = 1
    for x in xs:
        prev = 0
        le = []
        for m in range(1, x + 2):
            v = nv; nv += 1
            edges.append((prev, v))
            le.append(len(edges) - 1)
            prev = v
        legs.append(le)
    return nv, edges, legs


class Tree:
    def __init__(self, nv, edges):
        self.nv = nv
        self.edges = edges
        self.inc = [[] for _ in range(nv)]
        for k, (u, v) in enumerate(edges):
            self.inc[u].append(k)
            self.inc[v].append(k)

    def bad(self, pos, w):
        # sink or source at w?
        if not self.inc[w]:
            return False
        ins = outs = 0
        for k in self.inc[w]:
            st = pos[k]
            if st == 0:
                return False
            u, v = self.edges[k]
            head = v if st == 1 else u
            if head == w:
                ins += 1
            else:
                outs += 1
        return ins == 0 or outs == 0

    def moves(self, pos):
        res = []
        for k, st in enumerate(pos):
            if st:
                continue
            u, v = self.edges[k]
            for o in (1, 2):
                p = list(pos); p[k] = o; p = tuple(p)
                if not self.bad(p, u) and not self.bad(p, v):
                    res.append(p)
        return res


def grundy_all(tree):
    memo = {}

    def g(pos):
        if pos in memo:
            return memo[pos]
        S = set(g(q) for q in tree.moves(pos))
        m = 0
        while m in S:
            m += 1
        memo[pos] = m
        return m
    start = tuple([0] * len(tree.edges))
    g(start)
    return memo


def decompose(xs, legs, edges, pos):
    """spider state (s; L) and detached-run value of a raw position"""
    ins = outs = 0
    L = []
    det = 0
    for t, x in enumerate(xs):
        le = legs[t]
        dirs = []  # direction of each edge: 0 unmarked, 'I' or 'O'
        for k in le:
            st = pos[k]
            if st == 0:
                dirs.append(0)
            else:
                u, v = edges[k]          # u nearer the centre
                dirs.append('O' if st == 1 else 'I')
        # centre arc
        if dirs[0] == 'I':
            ins += 1
        elif dirs[0] == 'O':
            outs += 1
        marked = [m for m in range(len(dirs)) if dirs[m]]
        assert (x) not in marked  # pendant (index x) never marked
        if not marked:
            L.append((x, 'F'))
            continue
        if marked[0] > 0:
            L.append((marked[0], dirs[marked[0]]))
        # runs beyond the first arc
        for a_i, a in enumerate(marked):
            nxt = marked[a_i + 1] if a_i + 1 < len(marked) else None
            if nxt is None:
                ln = x - 1 - a          # unmarked edges a+1..x-1 (0-based), pendant is index x
                det ^= SP.rho(ln, dirs[a], 'F')
            else:
                ln = nxt - a - 1
                if ln > 0:
                    det ^= SP.rho(ln, dirs[a], dirs[nxt])
    if ins and outs:
        s = 'f'
    elif ins:
        s = 'i'
    elif outs:
        s = 'o'
    else:
        s = 'n'
    return s, SP.norm(L), det


def check_spider(xs, verbose=True):
    nv, edges, legs = build_spider(xs)
    tree = Tree(nv, edges)
    memo = grundy_all(tree)
    bad = 0
    for pos, gval in memo.items():
        s, L, det = decompose(xs, legs, edges, pos)
        pred = SP.Gamma(s, L) ^ det
        if pred != gval:
            bad += 1
            if bad <= 5:
                print('MISMATCH', xs, pos, s, L, det, pred, gval)
    start = tuple([0] * len(edges))
    if verbose:
        print(f'spider {xs}: {len(memo)} reachable positions, raw g={memo[start]}, '
              f'Prop6.1 g={SP.spider(*xs)}, mismatches={bad}')
    return bad, memo[start]


# ---------- raw brute force on status-labelled paths (Thm 4.3) -------------
def labelled_forest_grundy(nv, edges, status):
    """arrow game on a status-labelled forest (Definition 3.3 / Lemma 3.2)."""
    def mul(s, a):
        if a == 'o':
            return {'n': 'o', 'i': 'f', 'o': 'o', 'f': 'f'}[s]
        return {'n': 'i', 'i': 'i', 'o': 'f', 'f': 'f'}[s]

    @lru_cache(maxsize=None)
    def g(alive, st):
        deg = [0] * nv
        for k in alive:
            u, v = edges[k]
            deg[u] += 1; deg[v] += 1
        S = set()
        for k in alive:
            a, b = edges[k]
            for (u, v) in ((a, b), (b, a)):
                if (deg[u] >= 2 or st[u] in 'if') and (deg[v] >= 2 or st[v] in 'of'):
                    ns = list(st); ns[u] = mul(st[u], 'o'); ns[v] = mul(st[v], 'i')
                    S.add(g(tuple(x for x in alive if x != k), ''.join(ns)))
        m = 0
        while m in S:
            m += 1
        return m
    return g(tuple(range(len(edges))), ''.join(status))


def check_runs(kmax=10):
    # alpha: 'F' free, 'R' blocked right (s=i at left end), etc. per Def 4.1
    left = {'F': 'f', 'R': 'i', 'L': 'o'}
    right = {'F': 'f', 'R': 'o', 'L': 'i'}
    bad = 0
    for k in range(1, kmax + 1):
        edges = [(m - 1, m) for m in range(1, k + 1)]
        for (al, be, name, f) in [('F', 'F', 'A', SP.A), ('F', 'R', 'B', SP.B),
                                   ('R', 'R', 'C', SP.C), ('R', 'L', 'D', SP.D)]:
            st = ['n'] * (k + 1)
            st[0] = left[al]; st[k] = right[be]
            gv = labelled_forest_grundy(k + 1, edges, st)
            if gv != f(k):
                bad += 1
                print('RUN MISMATCH', name, k, gv, f(k))
    print(f'runs A,B,C,D checked by raw labelled-path brute force for k<={kmax}: mismatches={bad}')
    return bad


if __name__ == '__main__':
    check_runs(11)
    tot = 0
    for xs in [(1, 2, 1), (1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 2, 6), (1, 4, 2), (1, 4, 3), (1, 4, 4),
               (1, 4, 5), (1, 4, 6), (1, 6, 2), (1, 6, 3), (1, 6, 4), (2, 3, 4), (1, 3, 7), (1, 2, 7),
               (2, 2, 3), (1, 2, 3, 2), (1, 1, 2, 3), (2, 3, 5), (1, 2, 8), (1, 4, 7), (1, 8, 2)]:
        b, _ = check_spider(xs)
        tot += b
    print('TOTAL mismatches', tot)
