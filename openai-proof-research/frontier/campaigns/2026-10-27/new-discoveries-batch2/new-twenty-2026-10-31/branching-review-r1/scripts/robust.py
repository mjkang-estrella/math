"""Robustness of the D_m mechanism (review lane, independent code).

Design: A = complete digraph on m vertices a_1..a_m (indices 0..m-1); B = a digraph G on 4
vertices; two entries a_1->h1, a_2->h2 and two exits t1->a_1, t2->a_m (h's, t's in B, repeats
allowed).  Exhaustive search (sound pruning only) decides for each root in A whether a
non-separating out-branching exists.

mode 'w1'   : G = W1 fixed, all 16*16 (h1,h2,t1,t2) patterns, m = 3 and m = 4.
mode 'semi' : G ranges over all 3^6 = 729 labelled semicomplete digraphs on 4 vertices
              (each pair: one of the two arcs or the 2-cycle), all 256 patterns, m = 3.
              Reports every configuration with lambda >= 2, alpha = 2 and at least one failing
              root in A, grouped by the isomorphism class of G.
mode 'extra': D_m (m = 3, 4) plus ONE extra arc between A and B (every possible one), to see
              whether the failure is fragile.
usage: robust.py mode
"""
import sys, json, itertools


def masks(n, arcs):
    out = [0] * n; inn = [0] * n
    for (u, v) in arcs:
        out[u] |= 1 << v; inn[v] |= 1 << u
    return out, inn


def reach(start, adj):
    seen = 1 << start; fr = seen
    while fr:
        nx = 0; f = fr
        while f:
            b = f & -f; nx |= adj[b.bit_length() - 1]; f ^= b
        nx &= ~seen; seen |= nx; fr = nx
    return seen


def strong_masks(n, out, inn):
    full = (1 << n) - 1
    return reach(0, out) == full and reach(0, inn) == full


def two_arc_strong(n, arcs):
    out, inn = masks(n, arcs)
    if not strong_masks(n, out, inn):
        return False
    for (u, v) in arcs:
        out[u] ^= 1 << v; inn[v] ^= 1 << u
        ok = strong_masks(n, out, inn)
        out[u] ^= 1 << v; inn[v] ^= 1 << u
        if not ok:
            return False
    return True


def alpha_is_2(n, arcs):
    adj = [set() for _ in range(n)]
    for (u, v) in arcs:
        adj[u].add(v); adj[v].add(u)
    pair = any(j not in adj[i] for i in range(n) for j in range(i + 1, n))
    triple = any(j not in adj[i] and k not in adj[i] and k not in adj[j]
                 for i, j, k in itertools.combinations(range(n), 3))
    return pair and not triple


def has_nonsep(n, arcs, s):
    out, inn = masks(n, arcs)
    order = [v for v in range(n) if v != s]
    inl = {v: [u for u in range(n) if (inn[v] >> u) & 1] for v in range(n)}
    parent = [-1] * n; used = [0] * n; full = (1 << n) - 1

    def cyc(v, u):
        w = u
        while w != -1:
            if w == v:
                return True
            w = parent[w]
        return False

    def rec(i):
        if i == len(order):
            ro = [out[v] & ~used[v] for v in range(n)]
            ri = [0] * n
            for v in range(n):
                h = ro[v]
                while h:
                    b = h & -h; ri[b.bit_length() - 1] |= 1 << v; h ^= b
            return reach(0, ro) == full and reach(0, ri) == full
        v = order[i]
        for u in inl[v]:
            if cyc(v, u) or (out[u] & ~(used[u] | (1 << v))) == 0:
                continue
            parent[v] = u; used[u] |= 1 << v
            if rec(i + 1):
                return True
            used[u] &= ~(1 << v); parent[v] = -1
        return False
    return rec(0)


W1 = [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3), (3, 1)]


def build(m, G, h1, h2, t1, t2, extra=()):
    arcs = set((i, j) for i in range(m) for j in range(m) if i != j)
    for (u, v) in G:
        arcs.add((m + u, m + v))
    arcs |= {(0, m + h1), (1, m + h2), (m + t1, 0), (m + t2, m - 1)}
    arcs |= set(extra)
    return m + 4, sorted(arcs)


def analyse(m, G, h1, h2, t1, t2, extra=()):
    n, arcs = build(m, G, h1, h2, t1, t2, extra)
    if len(arcs) != len(set(arcs)):
        return None
    if not two_arc_strong(n, arcs) or not alpha_is_2(n, arcs):
        return None
    return [s for s in range(m) if not has_nonsep(n, arcs, s)]


def canon(G):
    best = None
    for p in itertools.permutations(range(4)):
        key = tuple(sorted((p[u], p[v]) for (u, v) in G))
        if best is None or key < best:
            best = key
    return best


def main():
    mode = sys.argv[1]
    res = {"mode": mode}
    if mode == "w1":
        for m in (3, 4):
            hits = []
            eligible = 0
            for h1, h2, t1, t2 in itertools.product(range(4), repeat=4):
                fr = analyse(m, W1, h1, h2, t1, t2)
                if fr is None:
                    continue
                eligible += 1
                if fr:
                    hits.append({"entries_heads": ["p%d" % (h1 + 1), "p%d" % (h2 + 1)],
                                 "exit_tails": ["p%d" % (t1 + 1), "p%d" % (t2 + 1)],
                                 "failing_A_roots": ["a%d" % (s + 1) for s in fr]})
            res["m%d" % m] = {"eligible_patterns(lambda>=2,alpha=2)": eligible, "patterns_with_failing_A_root": hits}
    elif mode == "semi":
        m = 3
        pairs = list(itertools.combinations(range(4), 2))
        classes = {}
        eligible = 0
        for states in itertools.product(range(3), repeat=6):
            G = []
            for (i, j), st in zip(pairs, states):
                if st in (0, 2):
                    G.append((i, j))
                if st in (1, 2):
                    G.append((j, i))
            for h1, h2, t1, t2 in itertools.product(range(4), repeat=4):
                fr = analyse(m, G, h1, h2, t1, t2)
                if fr is None:
                    continue
                eligible += 1
                if fr:
                    c = canon(G)
                    d = classes.setdefault(str(c), {"labelled_hits": 0, "all_A_fail": 0, "example": None})
                    d["labelled_hits"] += 1
                    if len(fr) == m:
                        d["all_A_fail"] += 1
                    if d["example"] is None:
                        d["example"] = {"G": G, "heads": [h1, h2], "tails": [t1, t2], "failing": fr}
        res["eligible_configs"] = eligible
        res["hit_classes"] = classes
        res["W1_canonical"] = str(canon(W1))
    elif mode == "extra":
        for m in (3, 4):
            out = []
            cands = [(a, m + b) for a in range(m) for b in range(4)] + [(m + b, a) for a in range(m) for b in range(4)]
            base = set(build(m, W1, 0, 2, 2, 2)[1])
            for e in cands:
                if e in base:
                    continue
                fr = analyse(m, W1, 0, 2, 2, 2, extra=(e,))
                nm = lambda x: ("a%d" % (x + 1)) if x < m else ("p%d" % (x - m + 1))
                out.append({"extra_arc": nm(e[0]) + nm(e[1]),
                            "failing_A_roots": None if fr is None else ["a%d" % (s + 1) for s in fr]})
            res["m%d" % m] = out
    print(json.dumps(res, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
