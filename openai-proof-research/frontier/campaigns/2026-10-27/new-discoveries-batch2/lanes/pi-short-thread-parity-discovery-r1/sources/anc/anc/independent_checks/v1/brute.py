"""Raw-rules brute force for the Game of Arrows on spiders, and a position-by-position
comparison with the spider-state evaluation (Prop 6.1 + Thm 4.3) of spider.py."""
import sys, itertools, time
from spider import Gamma, rho, spider
sys.setrecursionlimit(100000)


def spider_tree(legs):
    """vertices: 0 = centre.  Returns edges list [(u,v)], with u closer to the centre,
    and leg_edges[t] = list of edge indices from the centre outwards (incl. pendant)."""
    edges, leg_edges, nv = [], [], 1
    for x in legs:
        prev, idxs = 0, []
        for p in range(x + 1):
            edges.append((prev, nv)); idxs.append(len(edges) - 1)
            prev = nv; nv += 1
        leg_edges.append(idxs)
    return nv, edges, leg_edges


class Brute:
    def __init__(self, nv, edges):
        self.nv, self.edges = nv, edges
        self.inc = [[] for _ in range(nv)]
        for i, (u, v) in enumerate(edges):
            self.inc[u].append(i); self.inc[v].append(i)
        self.memo = {}

    def bad_vertex(self, pos, w):
        """sink or source?  state 1 = u->v, 2 = v->u"""
        ins = outs = 0
        for i in self.inc[w]:
            st = pos[i]
            if st == 0:
                return False
            u, v = self.edges[i]
            head = v if st == 1 else u
            if head == w:
                ins += 1
            else:
                outs += 1
        return ins == 0 or outs == 0

    def moves(self, pos):
        for i, st in enumerate(pos):
            if st:
                continue
            u, v = self.edges[i]
            for o in (1, 2):
                p2 = pos[:i] + (o,) + pos[i + 1:]
                if not self.bad_vertex(p2, u) and not self.bad_vertex(p2, v):
                    yield p2

    def g(self, pos):
        m = self.memo.get(pos)
        if m is not None:
            return m
        S = {self.g(p2) for p2 in self.moves(pos)}
        r = 0
        while r in S:
            r += 1
        self.memo[pos] = r
        return r


def state_value(legs, leg_edges, pos):
    """value via spider states: Gamma(s;L) xor detached runs.  edge state 1 = OUT, 2 = IN."""
    D = {1: 'O', 2: 'I'}
    cin = cout = False
    L, tot = [], 0
    for t, x in enumerate(legs):
        idx = leg_edges[t][:x]          # markable edges only
        st = [pos[i] for i in idx]
        marked = [p for p in range(x) if st[p]]
        if st[0] == 1: cout = True
        if st[0] == 2: cin = True
        if not marked:
            L.append((x, 'F'))
            continue
        p0 = marked[0]
        if p0 >= 1:
            L.append((p0, D[st[p0]]))
        for a, b in zip(marked, marked[1:]):
            tot ^= rho(b - a - 1, D[st[a]], D[st[b]])
        last = marked[-1]
        tot ^= rho(x - 1 - last, D[st[last]], 'F')
        # pendant edge must be unmarked
        assert pos[leg_edges[t][x]] == 0
    s = 'f' if (cin and cout) else 'i' if cin else 'o' if cout else 'n'
    return tot ^ Gamma(s, tuple(sorted(L)))


def check_all_positions(legs):
    nv, edges, le = spider_tree(legs)
    b = Brute(nv, edges)
    start = tuple([0] * len(edges))
    seen, st = {start}, [start]
    while st:
        p = st.pop()
        for q in b.moves(p):
            if q not in seen:
                seen.add(q); st.append(q)
    bad = 0
    for p in seen:
        if b.g(p) != state_value(legs, le, p):
            bad += 1
    return len(seen), bad, b.g(start)


if __name__ == '__main__':
    t0 = time.time()
    # (1) whole-spider values against the raw rules
    mism = 0; cnt = 0
    for x in range(1, 7):
        for y in range(x, 8):
            for z in range(y, 12):
                if x + y + z > 12:
                    continue
                nv, edges, le = spider_tree((x, y, z))
                bv = Brute(nv, edges).g(tuple([0] * len(edges)))
                sv = spider(x, y, z)
                cnt += 1
                if bv != sv:
                    mism += 1; print('MISMATCH', x, y, z, bv, sv)
    print('three-leg spiders with x+y+z<=12: %d compared, %d mismatches (%.1fs)' % (cnt, mism, time.time() - t0))
    # (2) every reachable position of some spiders
    for legs in [(2, 3, 5), (1, 3, 7), (2, 3, 6), (1, 2, 4, 2), (2, 2, 3, 3), (3, 4, 4)]:
        t0 = time.time()
        n, bad, g0 = check_all_positions(legs)
        print('S%s: %d reachable positions, %d mismatches, g=%d (%.1fs)' % (legs, n, bad, g0, time.time() - t0))
