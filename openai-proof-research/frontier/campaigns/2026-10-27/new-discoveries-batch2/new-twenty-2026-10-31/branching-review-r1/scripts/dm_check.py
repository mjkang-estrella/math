"""Independent brute-force check of D_m (review lane branching-review-r1).

Written from the source definitions only; nothing is imported from the discovery lane.

Vertices: a_1..a_m are 0..m-1; p1..p4 are m..m+3.
Arcs: complete digraph on A; W1 = {p1p2,p2p3,p3p4,p4p1,p1p3,p2p4,p4p2};
entries a_1p1, a_2p3; exits p3a_1, p3a_m.

For every root s it decides, by exhaustive search over ALL out-branchings rooted at s
(parent choice for each non-root vertex, cycles excluded), whether some out-branching F has
D \\ A(F) strongly connected.  The only pruning used is a necessary condition (every vertex
must keep at least one out-arc outside F), so no candidate F with D \\ A(F) strong is skipped.

It also checks: lambda(D) by the source definition (minimum out-degree of a nonempty proper
vertex subset) and by the Lean-draft definition (strong, and strong after deleting any one arc);
alpha(D) by brute force over all vertex subsets; and, for roots in A, whether arc-disjoint
B_s^+ and B_s^- exist (relevant to Conjecture 6 of [2]).

usage: dm_check.py m_min m_max [--goodpair]
"""
import sys, json, time


def build_dm(m):
    n = m + 4
    A = list(range(m))
    p1, p2, p3, p4 = m, m + 1, m + 2, m + 3
    arcs = set()
    for i in A:
        for j in A:
            if i != j:
                arcs.add((i, j))
    for (u, v) in [(p1, p2), (p2, p3), (p3, p4), (p4, p1), (p1, p3), (p2, p4), (p4, p2)]:
        arcs.add((u, v))
    arcs.add((0, p1)); arcs.add((1, p3))
    arcs.add((p3, 0)); arcs.add((p3, m - 1))
    return n, arcs


def masks(n, arcs):
    out = [0] * n
    inn = [0] * n
    for (u, v) in arcs:
        out[u] |= 1 << v
        inn[v] |= 1 << u
    return out, inn


def reach(start, adj, n):
    seen = 1 << start
    frontier = seen
    while frontier:
        nxt = 0
        f = frontier
        while f:
            b = f & -f
            v = b.bit_length() - 1
            nxt |= adj[v]
            f ^= b
        nxt &= ~seen
        seen |= nxt
        frontier = nxt
    return seen


def strong(n, out, inn):
    full = (1 << n) - 1
    return reach(0, out, n) == full and reach(0, inn, n) == full


def lam_cut(n, arcs):
    """Source definition: min over nonempty proper X of d^+(X)."""
    best = None
    full = (1 << n) - 1
    for X in range(1, full):
        c = 0
        for (u, v) in arcs:
            if (X >> u) & 1 and not (X >> v) & 1:
                c += 1
        if best is None or c < best:
            best = c
    return best


def two_arc_strong_literal(n, arcs):
    out, inn = masks(n, arcs)
    if not strong(n, out, inn):
        return False
    for (u, v) in arcs:
        out[u] ^= 1 << v; inn[v] ^= 1 << u
        ok = strong(n, out, inn)
        out[u] ^= 1 << v; inn[v] ^= 1 << u
        if not ok:
            return False
    return True


def alpha(n, arcs):
    adj = [0] * n
    for (u, v) in arcs:
        adj[u] |= 1 << v; adj[v] |= 1 << u
    best = 0
    for X in range(1 << n):
        k = bin(X).count("1")
        if k <= best:
            continue
        ok = True
        Y = X
        while Y:
            b = Y & -Y
            v = b.bit_length() - 1
            if adj[v] & X:
                ok = False
                break
            Y ^= b
        if ok:
            best = k
    return best


def search(n, arcs, s, mode):
    """mode 'nonsep': find out-branching F rooted at s with D - F strong.
       mode 'goodpair': find out-branching F rooted at s such that every vertex reaches s in D - F
       (i.e. D - F contains an in-branching rooted at s).
       Returns (found, number_of_complete_branchings_examined, witness_parent_list)."""
    out, inn = masks(n, arcs)
    order = [v for v in range(n) if v != s]
    inlist = {v: [u for u in range(n) if (inn[v] >> u) & 1] for v in range(n)}
    parent = [-1] * n
    used_out = [0] * n  # out-arcs of each vertex used by F (bitmask of heads)
    count = [0]
    full = (1 << n) - 1
    result = [None]

    def creates_cycle(v, u):
        # adding arc u->v (u parent of v): cycle iff v is an ancestor of u
        w = u
        while w != -1:
            if w == v:
                return True
            w = parent[w]
        return False

    def rec(i):
        if i == len(order):
            # all non-root vertices have parents and no cycles -> F is an out-branching rooted at s
            count[0] += 1
            rout = [out[v] & ~used_out[v] for v in range(n)]
            rin = [0] * n
            for v in range(n):
                hv = rout[v]
                while hv:
                    b = hv & -hv
                    w = b.bit_length() - 1
                    rin[w] |= 1 << v
                    hv ^= b
            if mode == "nonsep":
                ok = reach(0, rout, n) == full and reach(0, rin, n) == full
            else:
                ok = reach(s, rin, n) == full
            if ok:
                result[0] = list(parent)
                return True
            return False
        v = order[i]
        for u in inlist[v]:
            if creates_cycle(v, u):
                continue
            # necessary-condition prune (sound only for nonsep): u must keep an out-arc outside F
            if mode == "nonsep" and (out[u] & ~(used_out[u] | (1 << v))) == 0:
                continue
            parent[v] = u
            used_out[u] |= 1 << v
            if rec(i + 1):
                return True
            used_out[u] &= ~(1 << v)
            parent[v] = -1
        return False

    found = rec(0)
    return found, count[0], result[0]


def name(m, v):
    return "a%d" % (v + 1) if v < m else "p%d" % (v - m + 1)


def main():
    m0, m1 = int(sys.argv[1]), int(sys.argv[2])
    goodpair = "--goodpair" in sys.argv
    summary = []
    for m in range(m0, m1 + 1):
        t0 = time.time()
        n, arcs = build_dm(m)
        lc = lam_cut(n, arcs)
        tas = two_arc_strong_literal(n, arcs)
        al = alpha(n, arcs)
        indeg = [sum(1 for (u, v) in arcs if v == x) for x in range(n)]
        rec = {"m": m, "n": n, "arcs": len(arcs), "lambda_cut": lc, "two_arc_strong_literal": tas,
               "alpha": al, "min_indegree": min(indeg), "roots": {}}
        for s in range(n):
            found, cnt, wit = search(n, arcs, s, "nonsep")
            entry = {"nonsep_found": found, "branchings_examined": cnt}
            if found:
                entry["witness_arcs"] = sorted("%s%s" % (name(m, wit[v]), name(m, v)) for v in range(n) if v != s)
            if goodpair and s < m:
                gf, gc, gw = search(n, arcs, s, "goodpair")
                entry["goodpair_same_root_found"] = gf
                entry["goodpair_branchings_examined"] = gc
            rec["roots"][name(m, s)] = entry
        rec["failing_roots"] = [r for r, e in rec["roots"].items() if not e["nonsep_found"]]
        rec["seconds"] = round(time.time() - t0, 2)
        print(json.dumps(rec, sort_keys=True))
        sys.stdout.flush()
        summary.append((m, rec["failing_roots"]))
    for m, fr in summary:
        print("m=%d failing roots: %s" % (m, ",".join(fr)))


if __name__ == "__main__":
    main()
