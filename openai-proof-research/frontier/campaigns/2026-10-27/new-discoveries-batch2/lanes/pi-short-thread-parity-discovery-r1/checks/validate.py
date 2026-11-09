"""
Validation battery for the two solvers against known results of
arXiv:2610.15145v1 (values only; the paper's *proofs* are never used).

Targets read directly from the source text:
  - Theorem 4.3: A_k=C_k=k mod 2, B_k=k, D_k=1 (k>=2 even) else 0.
  - g(S(1,3,7)) = 0, g(S(1,4,6)) = 0 (Theorem 7.1(b)); m = 11 odd.
  - H(3,1|3|4,1): g = 2, m = 12; H(5,2|1|3,1): g = 4, m = 12 (Thm 7.1(c)).
  - Theorem 10.11: the piece of T_21 has 16 vertices, 15 edges, g = 3.
  - Corollary 5.7: g(S(x,x,y1..yr)) = (y1+..+yr) mod 2.
  - Theorem 10.3 on random clean status trees: g = |E| mod 2.
  - fast solver == raw sink/source solver on many random trees/pieces.
  - global i<->o reversal invariance of the fast solver.
"""
import random
import sys
sys.path.insert(0, '.')
from cycles_solver import Solver, canon, piece_status, g_piece, g_tree, tree_pieces
import raw_checker


def run_form(k, a, b):
    """Path v0..vk with end statuses from alpha/beta in {*,>,<}."""
    st = [0] * (k + 1)
    st[0] = {'*': 3, '>': 1, '<': 2}[a]
    st[k] = {'*': 3, '>': 2, '<': 1}[b] if k >= 1 else st[0]
    edges = [(i, i + 1) for i in range(k)]
    return k + 1, edges, tuple(st)


def check_runs():
    ok = True
    for k in range(0, 11):
        s = Solver()
        vals = {}
        for name, a, b in (('A', '*', '*'), ('B', '*', '>'), ('C', '>', '>'), ('D', '>', '<')):
            n, edges, st = run_form(k, a, b)
            vals[name] = s.g(canon(n, edges, st)) if k >= 1 else 0
        expA = k % 2
        expB = k
        expC = k % 2
        expD = 1 if (k >= 2 and k % 2 == 0) else 0
        if not (vals['A'] == expA and vals['B'] == expB and vals['C'] == expC and vals['D'] == expD):
            print(f"RUN FAIL k={k}: {vals} expected A={expA} B={expB} C={expC} D={expD}")
            ok = False
    print("runs (Thm 4.3):", "PASS" if ok else "FAIL")
    return ok


def spider_tree(legs):
    """Tree S(x1..xk): centre + legs of x_t+1 edges. Returns (n, edges)."""
    edges = []
    nxt = 1
    for x in legs:
        prev = 0
        for _ in range(x + 1):
            edges.append((prev, nxt))
            prev = nxt
            nxt += 1
    return nxt, edges


def h_tree(a1, a2, l, b1, b2):
    """H(a1,a2|l|b1,b2): u,v joined by path of l edges; legs of a1,a2,b1,b2
    markable edges, each leg ending in a pendant edge."""
    # vertices: u=0, v=1, path interiors 2..l, then legs
    edges = []
    # path u=0 - v1 .. v_{l-1} - v=l+1?  build: path vertices 0, 2, 3, ..., l, 1
    path = [0] + list(range(2, l + 1)) + [1]  # l+1 edges total between u and v
    for i in range(len(path) - 1):
        edges.append((path[i], path[i + 1]))
    nxt = l + 1

    def leg(root, a):
        nonlocal nxt
        prev = root
        for _ in range(a + 1):
            edges.append((prev, nxt))
            prev = nxt
            nxt += 1
    leg(0, a1)
    leg(0, a2)
    leg(1, b1)
    leg(1, b2)
    return nxt, edges


def markable(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return sum(1 for u, v in edges if deg[u] > 1 and deg[v] > 1)


def t21_piece():
    """The piece of T_21 (Theorem 10.11): u-v path of 3 edges; u legs 2,3;
    v leg 2 and edge v-w; w legs 1,3.  Piece = tree minus pendant edges with
    f-leaves.  16 vertices, 15 edges."""
    # build the piece directly: leaves f, interiors n
    edges = []
    # u=0, path a=1,b=2, v=3
    edges += [(0, 1), (1, 2), (2, 3)]
    # u legs: 2 edges (0-4-5), 3 edges (0-6-7-8)
    edges += [(0, 4), (4, 5), (0, 6), (6, 7), (7, 8)]
    # v leg 2: (3-9-10); v-w: (3-11); w=11 legs 1: (11-12), 3: (11-13-14-15)
    edges += [(3, 9), (9, 10), (3, 11), (11, 12), (11, 13), (13, 14), (14, 15)]
    return 16, edges


def main():
    allok = True

    allok &= check_runs()

    # S(1,3,7), S(1,4,6)
    for legs, expg, expm in (((1, 3, 7), 0, 11), ((1, 4, 6), 0, 11)):
        n, edges = spider_tree(legs)
        assert markable(n, edges) == expm, (legs, markable(n, edges))
        s = Solver()
        g = g_tree(s, n, edges)
        ok = g == expg
        print(f"g(S{legs}) = {g} (expect {expg}):", "PASS" if ok else "FAIL")
        allok &= ok

    # Corollary 5.7: S(x,x,y1..yr)
    ok = True
    for legs in ((2, 2, 3), (3, 3, 1, 4), (1, 1, 2, 5), (2, 2), (2, 2, 2, 3), (1, 1, 7), (3, 3, 3, 2)):
        ys = legs[2:]
        n, edges = spider_tree(legs)
        s = Solver()
        g = g_tree(s, n, edges)
        exp = sum(ys) % 2
        if g != exp:
            print(f"C5.7 FAIL S{legs}: g={g} expected {exp}")
            ok = False
    print("Corollary 5.7 twins:", "PASS" if ok else "FAIL")
    allok &= ok

    # H-trees
    for (a1, a2, l, b1, b2, expg, expm) in ((3, 1, 3, 4, 1, 2, 12), (5, 2, 1, 3, 1, 4, 12)):
        n, edges = h_tree(a1, a2, l, b1, b2)
        assert len(edges) + 1 == 17
        assert markable(n, edges) == expm, markable(n, edges)
        s = Solver()
        g = g_tree(s, n, edges)
        ok = g == expg
        print(f"g(H({a1},{a2}|{l}|{b1},{b2})) = {g} (expect {expg}):", "PASS" if ok else "FAIL")
        allok &= ok

    # T_21 piece
    n, edges = t21_piece()
    s = Solver()
    g = g_piece(s, n, edges)
    ok = (g == 3)
    print(f"g(piece of T_21) = {g} (expect 3), edges={len(edges)}:", "PASS" if ok else "FAIL")
    allok &= ok

    # random clean status trees: g = |E| mod 2 (Theorem 10.3).
    # clean: leaves free, no chain edges, statuses n/i/o on non-leaves.
    rng = random.Random(20261028)
    ok = True
    for trial in range(400):
        # random clean tree: random tree, then subdivide: ensure no deg-2 chains:
        # easiest: random tree where every non-leaf vertex keeps degree != 2
        # build from a random series-reduced skeleton by attaching f-leaves.
        k = rng.randint(2, 6)
        # random labelled skeleton on k vertices, then prune to series-reduced
        for _ in range(200):
            _, skel = random_labeled_tree(k, rng)
            deg = [0] * k
            for u, v in skel:
                deg[u] += 1
                deg[v] += 1
            if all(deg[i] != 2 for i in range(k)) and (k == 1 or min(deg) == 1):
                break
        else:
            continue
        # attach one f-leaf to every skeleton leaf
        n = k
        edges = list(skel)
        for i in range(k):
            if deg[i] == 1:
                edges.append((i, n))
                n += 1
        # random statuses on branch vertices
        st = [3 if len([1 for u, v in edges if u == i or v == i]) == 1 else 0 for i in range(n)]
        for i in range(n):
            if st[i] == 0:
                st[i] = rng.choice((0, 1, 2))
        s = Solver()
        g = s.g(canon(n, edges, tuple(st)))
        if g != len(edges) % 2:
            print("CLEAN FAIL", n, edges, st, g, len(edges) % 2)
            ok = False
            break
    print("Theorem 10.3 on random clean trees (400):", "PASS" if ok else "FAIL")
    allok &= ok

    # fast vs raw on random trees (small)
    ok = True
    for trial in range(120):
        k = rng.randint(2, 9)
        n, edges = random_labeled_tree(k, rng)  # already (n, edges)
        s = Solver()
        g1 = g_tree(s, n, edges)
        g2 = raw_checker.raw_g(n, edges)
        if g1 != g2:
            print("FAST/RAW MISMATCH", n, edges, g1, g2)
            ok = False
            break
    print("fast == raw on 120 random trees:", "PASS" if ok else "FAIL")
    allok &= ok

    # fast vs raw on random 3-thread pieces (the Q11.4 novel structure)
    ok = True
    for trial in range(60):
        n, edges = random_q114_piece(rng, 8, 12)
        s = Solver()
        g1 = g_piece(s, n, edges)
        # realize: attach a pendant leaf to every piece leaf; raw runs on T
        deg = [0] * n
        for u, v in edges:
            deg[u] += 1
            deg[v] += 1
        T_edges = list(edges)
        T_n = n
        for i in range(n):
            if deg[i] == 1:
                T_edges.append((i, T_n))
                T_n += 1
        g2 = raw_checker.raw_g(T_n, T_edges)
        if g1 != g2:
            print("FAST/RAW MISMATCH piece", n, edges, g1, g2)
            ok = False
            break
    print("fast == raw on 60 random 3-thread pieces:", "PASS" if ok else "FAIL")
    allok &= ok

    # i<->o reversal invariance: g(X) == g(swap(X))
    ok = True
    for trial in range(100):
        n, edges = random_q114_piece(rng, 6, 14)
        deg = [0] * n
        for u, v in edges:
            deg[u] += 1
            deg[v] += 1
        st = [3 if deg[i] == 1 else 0 for i in range(n)]
        for i in range(n):
            if st[i] == 0 and rng.random() < 0.5:
                st[i] = rng.choice((1, 2))
        sw = tuple(1 if x == 2 else 2 if x == 1 else x for x in st)
        s = Solver()
        if s.g(canon(n, edges, tuple(st))) != s.g(canon(n, edges, sw)):
            print("REVERSAL FAIL", n, edges, st)
            ok = False
            break
    print("i<->o reversal invariance (100):", "PASS" if ok else "FAIL")
    allok &= ok

    print("ALL:", "PASS" if allok else "FAIL")
    return allok


def random_labeled_tree(k, rng):
    if k == 1:
        return 1, []
    par = [0] + [rng.randrange(i) for i in range(1, k)]
    edges = [(par[i], i) for i in range(1, k)]
    return k, edges


def random_q114_piece(rng, lo, hi):
    """Random piece: internal threads <= 2, leaf threads <= 3, leaves f."""
    # random series-reduced skeleton
    for _ in range(500):
        k = rng.randint(2, 6)
        _, skel = random_labeled_tree(k, rng)
        deg = [0] * k
        for u, v in skel:
            deg[u] += 1
            deg[v] += 1
        if k >= 2 and all(deg[i] != 2 for i in range(k)) and min(deg) == 1:
            break
    else:
        raise RuntimeError
    edges = []
    n = k
    for u, v in skel:
        if deg[u] >= 3 and deg[v] >= 3:
            w = rng.choice((1, 2))
        else:
            w = rng.choice((1, 2, 3))
        prev = u
        for _ in range(w - 1):
            edges.append((prev, n))
            prev = n
            n += 1
        edges.append((prev, v))
    return n, edges


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
