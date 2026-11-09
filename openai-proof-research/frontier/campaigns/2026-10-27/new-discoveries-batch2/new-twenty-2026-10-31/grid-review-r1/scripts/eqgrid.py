"""Independent exhaustive check of NSS Conjecture 5.6 on small grids P_m x P_n.

Written from scratch for lane grid-review-r1. It does NOT use the r131 scripts and does not
assume the r131 proof's structure (no row determinism, layers, or the group A0 as an input).

Method
  * Equitable partitions: exact split-and-cir enumeration.
      cir(A) = coarsest equitable refinement of A, by iterated neighbour-count refinement.
      Start at T = cir(single class). Every equitable B < A (A equitable) satisfies
      B <= cir(A') for some 2-split A' of a class of A that B splits, so a depth-first
      search over all 2-splits from T reaches every equitable partition. Every output of
      cir is equitable, and each one is re-checked against Definition 5.1 directly.
  * Brute-force mode (N <= 10 vertices): all set partitions are enumerated as
    restricted-growth strings and tested against Definition 5.1. This cross-checks the
    split-and-cir code.
  * Aut(G): all vertex permutations preserving adjacency, by exhaustive backtracking in BFS
    order (complete search with adjacency-consistency pruning). A0 is not assumed;
    it is compared afterwards.
  * Sub(Aut G): every subset containing the identity and closed under composition.
  * Orbit partitions, the map Phi : Sub -> EqPart, order-embedding test under refinement,
    and the trivial-stabilizer test in the full Aut(G).

Usage: eqgrid.py OUT.json SPEC [SPEC ...] where SPEC is "m x n" written as MxN, or
"brute:MxN" for the brute-force cross-check.
"""
import json
import sys
import time


def grid(m, n):
    N = m * n
    adj = [[] for _ in range(N)]
    for i in range(m):
        for j in range(n):
            v = i * n + j
            if i + 1 < m:
                adj[v].append(v + n); adj[v + n].append(v)
            if j + 1 < n:
                adj[v].append(v + 1); adj[v + 1].append(v)
    return [sorted(a) for a in adj]


def canon(lab):
    seen = {}
    out = []
    for x in lab:
        if x not in seen:
            seen[x] = len(seen)
        out.append(seen[x])
    return tuple(out)


def cir(adj, lab):
    """Coarsest equitable refinement of the partition with labels lab."""
    lab = canon(lab)
    k = len(set(lab))
    while True:
        sig = [(lab[v], tuple(sorted(lab[w] for w in adj[v]))) for v in range(len(adj))]
        new = canon(sig)
        k2 = len(set(new))
        if k2 == k:
            return new
        lab, k = new, k2


def is_equitable(adj, lab):
    """Definition 5.1 checked literally: d_B(i) = d_B(j) for i, j in one cell, every cell B."""
    cells = {}
    for v, c in enumerate(lab):
        cells.setdefault(c, []).append(v)
    keys = sorted(cells)
    for c, vs in cells.items():
        prof = None
        for v in vs:
            cnt = {b: 0 for b in keys}
            for w in adj[v]:
                cnt[lab[w]] += 1
            p = tuple(cnt[b] for b in keys)
            if prof is None:
                prof = p
            elif p != prof:
                return False
    return True


SPLIT_CAP = 1 << 16


def enum_equitable(adj):
    N = len(adj)
    top = cir(adj, [0] * N)
    found = {top}
    stack = [top]
    nodes = 0
    cir_calls = 1
    while stack:
        A = stack.pop()
        nodes += 1
        cells = {}
        for v, c in enumerate(A):
            cells.setdefault(c, []).append(v)
        for c, C in cells.items():
            s = len(C)
            if s < 2:
                continue
            if (1 << (s - 1)) > SPLIT_CAP:
                raise RuntimeError("class of size %d exceeds split cap; not exhaustive" % s)
            rest = C[1:]
            for mask in range(0, 1 << (s - 1)):
                if mask == (1 << (s - 1)) - 1:
                    continue  # S = C is not a proper split
                lab = list(A)
                newc = N + 1
                # S = {C[0]} plus the members of rest selected by mask; the complement gets newc
                for t, v in enumerate(rest):
                    if not (mask >> t) & 1:
                        lab[v] = newc
                B = cir(adj, lab)
                cir_calls += 1
                if B not in found:
                    found.add(B)
                    stack.append(B)
    return found, nodes, cir_calls


def rgs_partitions(N):
    """All set partitions of range(N) as restricted-growth strings."""
    lab = [0] * N

    def rec(i, mx):
        if i == N:
            yield tuple(lab)
            return
        for c in range(mx + 2):
            lab[i] = c
            yield from rec(i + 1, max(mx, c))

    if N == 0:
        yield ()
        return
    lab[0] = 0
    yield from rec(1, 0)


def automorphisms(adj):
    N = len(adj)
    adjset = [set(a) for a in adj]
    deg = [len(a) for a in adj]
    # BFS order (grid is connected)
    order, seen = [], {0}
    q = [0]
    while q:
        v = q.pop(0)
        order.append(v)
        for w in adj[v]:
            if w not in seen:
                seen.add(w); q.append(w)
    assert len(order) == N
    pos = {v: k for k, v in enumerate(order)}
    f = [-1] * N
    used = [False] * N
    res = []

    def rec(k):
        if k == N:
            # full verification
            for v in range(N):
                for w in adj[v]:
                    if f[w] not in adjset[f[v]]:
                        return
            res.append(tuple(f))
            return
        v = order[k]
        prev = [u for u in adj[v] if pos[u] < k]
        if prev:
            cand = [w for w in adj[f[prev[0]]] if not used[w]]
        else:
            cand = [w for w in range(N) if not used[w]]
        for w in cand:
            if deg[w] != deg[v]:
                continue
            ok = True
            for u in order[:k]:
                if (u in adjset[v]) != (f[u] in adjset[w]):
                    ok = False
                    break
            if not ok:
                continue
            f[v] = w; used[w] = True
            rec(k + 1)
            f[v] = -1; used[w] = False

    rec(0)
    return res


def compose(g, h):  # (g o h)(v) = g[h[v]]
    return tuple(g[x] for x in h)


def subgroups(G):
    G = sorted(G)
    N = len(G[0])
    e = tuple(range(N))
    assert e in G
    others = [g for g in G if g != e]
    if len(G) > 16:
        raise RuntimeError("group too large for subset enumeration")
    subs = []
    for mask in range(1 << len(others)):
        S = {e} | {others[t] for t in range(len(others)) if (mask >> t) & 1}
        if all(compose(a, b) in S for a in S for b in S):
            subs.append(frozenset(S))
    return subs


def orbit_partition(H, N):
    parent = list(range(N))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for g in H:
        for v in range(N):
            a, b = find(v), find(g[v])
            if a != b:
                parent[a] = b
    return canon([find(v) for v in range(N)])


def refines(A, B):
    """A <= B in the source's order: every class of A lies inside a class of B."""
    m = {}
    for a, b in zip(A, B):
        if m.setdefault(a, b) != b:
            return False
    return True


def explicit_A0(m, n):
    N = m * n

    def perm(fn):
        return tuple(fn(i, j)[0] * n + fn(i, j)[1] for i in range(m) for j in range(n))

    gens = [perm(lambda i, j: (m - 1 - i, j)), perm(lambda i, j: (i, n - 1 - j))]
    if m == n:
        gens.append(perm(lambda i, j: (j, i)))
    e = tuple(range(N))
    grp = {e}
    frontier = [e]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                h = compose(s, g)
                if h not in grp:
                    grp.add(h); new.append(h)
        frontier = new
    return grp


MCKAY_EDGES = [(1, 2), (1, 3), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (6, 8), (7, 8)]


def mckay():
    """Control: the graph of the source's Figure 5.1 (two triangles joined by a path)."""
    adj = [[] for _ in range(8)]
    for a, b in MCKAY_EDGES:
        adj[a - 1].append(b - 1); adj[b - 1].append(a - 1)
    return [sorted(x) for x in adj]


def run(m, n, brute=False, control=False):
    t0 = time.process_time()
    adj = mckay() if control else grid(m, n)
    N = len(adj)
    rec = {"m": m, "n": n, "N": N, "control_mckay": control}
    eq, nodes, calls = enum_equitable(adj)
    rec["eq_count"] = len(eq)
    rec["search_nodes"] = nodes
    rec["cir_calls"] = calls
    rec["all_eq_pass_def51"] = all(is_equitable(adj, A) for A in eq)
    if brute:
        bf = set()
        total = 0
        for lab in rgs_partitions(N):
            total += 1
            if is_equitable(adj, lab):
                bf.add(canon(lab))
        rec["brute_total_partitions"] = total
        rec["brute_eq_count"] = len(bf)
        rec["brute_matches_splitcir"] = (bf == eq)
    aut = automorphisms(adj)
    rec["aut_order"] = len(aut)
    rec["aut_equals_A0"] = None if control else (set(aut) == explicit_A0(m, n))
    subs = subgroups(aut)
    rec["sub_count"] = len(subs)
    phi = {}
    for H in subs:
        phi[H] = orbit_partition(H, N)
    images = set(phi.values())
    rec["orbit_partition_count"] = len(images)
    rec["eq_equals_orbit_partitions"] = (images == eq)
    rec["non_orbit_equitable"] = [list(A) for A in sorted(eq - images)][:5]
    rec["orbit_not_equitable"] = [list(A) for A in sorted(images - eq)][:5]
    injective = len(images) == len(subs)
    rec["phi_injective"] = injective
    emb = True
    for H in subs:
        for K in subs:
            if (H <= K) != refines(phi[H], phi[K]):
                emb = False
    rec["phi_order_embedding"] = emb
    rec["phi_order_isomorphism_onto_EqPart"] = emb and images == eq
    free = [v for v in range(N) if all(g[v] != v for g in aut if g != tuple(range(N)))]
    rec["free_vertex_exists"] = bool(free)
    rec["free_vertices_example"] = [divmod(v, n) for v in free[:3]] if not control else free[:3]
    rec["exceptional_2le_m_eq_n_le3"] = (2 <= m == n <= 3)
    rec["prediction_holds"] = (
        rec["eq_equals_orbit_partitions"]
        and (rec["free_vertex_exists"] == (not rec["exceptional_2le_m_eq_n_le3"]))
        and (rec["phi_order_isomorphism_onto_EqPart"] == rec["free_vertex_exists"])
        and ((len(eq) == len(subs)) == rec["free_vertex_exists"])
    )
    rec["cpu_s"] = round(time.process_time() - t0, 3)
    return rec


def main():
    out = sys.argv[1]
    results = []
    for spec in sys.argv[2:]:
        if spec == "mckay":
            r = run(0, 0, brute=True, control=True)
            r["prediction_holds"] = None
            results.append(r)
            print(json.dumps(r), flush=True)
            continue
        brute = spec.startswith("brute:")
        if brute:
            spec = spec[6:]
        m, n = map(int, spec.lower().split("x"))
        r = run(m, n, brute)
        results.append(r)
        print(json.dumps({k: r[k] for k in r if k not in ("non_orbit_equitable", "orbit_not_equitable")}), flush=True)
        with open(out, "w") as fh:
            json.dump(results, fh, indent=1)
    print("DONE", len(results), "grids; all predictions hold:", all(r["prediction_holds"] for r in results if not r["control_mckay"]))


if __name__ == "__main__":
    main()
