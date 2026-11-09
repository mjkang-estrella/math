#!/usr/bin/env python3
"""Independent exact scan for Conjecture 3.6 (arXiv:1712.10010v2): D(T) < 2 cfc(T).

Decision rule per tree T (n >= 2), exact and complete:
  1. Compute D(T) exactly = min over priorities of Algorithm-1 depth
     (per-component min-size-diff edge, free tie-breaking; memoized on canonical form).
  2. If D < 2*max(Delta, ceil(log2 n))  =>  conjecture holds for T, because
     cfc(T) >= Delta (edges at a common vertex pairwise distinct: the 2-path
     through the vertex forces distinct colors) and cfc(T) >= ceil(log2 n)
     (source Theorem 2.5, parity-vector argument).  [AIRTIGHT lower bounds]
  3. Else (risk zone): search exhaustively for a conflict-free coloring with
     floor(D/2) colors. Found => counterexample certificate (cfc <= floor(D/2),
     D >= 2*floor(D/2) >= 2*cfc).  Not found => cfc > D/2 => conjecture holds.

Also validates source claims: d(P_n)=ceil(log2 n), d(K_{1,n-1})=n-1,
d(S_{a,b})=Delta, d(B_k)=k-1, and records D - 2*max(Delta,L) extremes and
D - Delta vs log2(n/Delta) patterns.
"""
import json, os, sys, itertools, math, datetime
from functools import lru_cache

# ---------- canonical form (AHU via centroids) ----------

def canon(n, edges):
    if n == 1:
        return "1"
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b); adj[b].append(a)
    # centroids by leaf peeling
    deg = [len(adj[v]) for v in range(n)]
    from collections import deque
    q = deque(v for v in range(n) if deg[v] <= 1)
    cut = [False] * n
    cnt = n
    last = []
    touch = deg[:]
    while cnt > 2:
        nxt = []
        for v in q:
            if cut[v]:
                continue
            cut[v] = True; cnt -= 1
            for w in adj[v]:
                touch[w] -= 1
                if touch[w] <= 1 and not cut[w]:
                    nxt.append(w)
        q = [v for v in nxt if not cut[v]]
        last = q[:]
    cents = [v for v in range(n) if not cut[v]] if cnt <= 2 else []
    if not cents:
        cents = [v for v in range(n) if not cut[v]][:1]
    def rooted(root):
        parent = [-1] * n
        order = [root]; parent[root] = root
        i = 0
        while i < len(order):
            v = order[i]; i += 1
            for w in adj[v]:
                if parent[w] == -1:
                    parent[w] = v; order.append(w)
        enc = [""] * n
        for v in reversed(order):
            ch = sorted(enc[w] for w in adj[v] if parent[w] == v and w != root or (parent[w] == v and w != root))
            ch = sorted(enc[w] for w in adj[v] if w != v and parent[w] == v)
            enc[v] = "(" + "".join(ch) + ")"
        return enc[root]
    encs = sorted(rooted(c) for c in cents)
    return f"{n}:" + "".join(encs)

# ---------- exact D ----------

memo_D = {}
def min_depth(n, edges):
    """edges: tuple of 2-tuples, vertices 0..n-1."""
    key = canon(n, edges)
    v = memo_D.get(key)
    if v is not None:
        return v
    if n == 1:
        memo_D[key] = 0
        return 0
    adj = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i)); adj[b].append((a, i))
    def side_without(eidx, src):
        # BFS from src avoiding edge eidx; return frozenset of vertices
        seen = {src}; stack = [src]
        while stack:
            x = stack.pop()
            for w, i in adj[x]:
                if i != eidx and w not in seen:
                    seen.add(w); stack.append(w)
        return seen
    infos = []
    for i, (a, b) in enumerate(edges):
        S = side_without(i, a)
        a_size = len(S)
        infos.append((i, a_size, S))
    mind = min(abs(n - 2 * a_size) for _, a_size, _ in infos)
    best = None
    for i, a_size, S in infos:
        if abs(n - 2 * a_size) != mind:
            continue
        T = set(range(n)) - S
        dA = comp_depth(S, edges, i)
        dB = comp_depth(T, edges, i)
        val = 1 + max(dA, dB)
        if best is None or val < best:
            best = val
    memo_D[key] = best
    return best

def comp_depth(vertices, edges, removed_idx):
    """Depth of the component induced by `vertices` after edge removed_idx is gone."""
    vs = sorted(vertices)
    idx = {v: i for i, v in enumerate(vs)}
    ee = []
    for j, (a, b) in enumerate(edges):
        if j == removed_idx:
            continue
        if a in idx and b in idx:
            ee.append((idx[a], idx[b]))
    if not ee:
        return 0
    return min_depth(len(vs), tuple(ee))

def D_of(n, edges):
    return min_depth(n, tuple(edges))

# ---------- exact cfc search (k colors?) ----------

def has_cf_coloring(n, edges, k):
    """Exhaustive backtracking: is there a CF-connected edge coloring with k colors?"""
    m = len(edges)
    if m == 0:
        return True
    adj = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i)); adj[b].append((a, i))
    # all paths with >= 2 edges, as frozenset of edge indices
    paths = set()
    for s in range(n):
        # DFS enumerating paths from s
        def dfs(v, parent, es):
            for w, i in adj[v]:
                if w == parent:
                    continue
                ne = es | {i}
                if len(ne) >= 2:
                    paths.add(frozenset(ne))
                dfs(w, v, ne)
        dfs(s, -1, frozenset())
    paths = [p for p in paths]
    # order edges: BFS from vertex of max degree to complete paths early
    order = []
    seen_e = set()
    start = max(range(n), key=lambda v: len(adj[v]))
    stack = [(start, -1)]
    while stack:
        v, pe = stack.pop()
        for w, i in adj[v]:
            if i not in seen_e:
                seen_e.add(i); order.append(i)
                stack.append((w, i))
    # edge -> paths that contain it
    e2p = [[] for _ in range(m)]
    for pi, p in enumerate(paths):
        for e in p:
            e2p[e].append(pi)
    remaining = [len(p) for p in paths]
    col = [-1] * m
    maxused = -1

    def path_ok(p):
        from collections import Counter
        cnt = Counter(col[e] for e in p)
        return any(v == 1 for v in cnt.values())

    def rec(oi):
        nonlocal maxused
        if oi == len(order):
            return True
        e = order[oi]
        lim = min(k - 1, maxused + 1)
        for c in range(lim + 1):
            a, b = edges[e]
            ok = True
            for w, i in adj[a]:
                if i != e and col[i] == c:
                    ok = False; break
            if ok:
                for w, i in adj[b]:
                    if i != e and col[i] == c:
                        ok = False; break
            if not ok:
                continue
            col[e] = c
            if c > maxused:
                maxused = c
            # check completed paths
            violated = False
            touched = []
            for pi in e2p[e]:
                remaining[pi] -= 1
                touched.append(pi)
                if remaining[pi] == 0 and not path_ok(paths[pi]):
                    violated = True
            if not violated:
                if rec(oi + 1):
                    return True
            for pi in touched:
                remaining[pi] += 1
            col[e] = -1
        return False

    return rec(0)

# ---------- enumeration of unlabeled trees ----------

def enumerate_unlabeled(N):
    """reps[n] = list of edge tuples (vertices 0..n-1)."""
    reps = {1: [()]}
    for n in range(2, N + 1):
        seen = {}
        out = []
        for edges in reps[n - 1]:
            for v in range(n - 1):
                e2 = tuple(edges) + ((v, n - 1),)
                c = canon(n, e2)
                if c not in seen:
                    seen[c] = e2
                    out.append(e2)
        reps[n] = out
    return reps

def max_delta(n, edges):
    deg = {}
    for a, b in edges:
        deg[a] = deg.get(a, 0) + 1
        deg[b] = deg.get(b, 0) + 1
    return max(deg.values())

def main():
    t0 = datetime.datetime.now(datetime.timezone.utc)
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    reps = enumerate_unlabeled(N)
    out = {"N": N, "generated_at": t0.isoformat(), "per_n": {}, "risk_trees": [],
           "violators_D_lt_2max": [], "source_claim_checks": {}, "max_slack": None}
    total = 0
    worst = None  # maximize D - 2*max(Delta, L)
    for n in range(2, N + 1):
        cnt = 0; risk = 0; ok_trivial = 0
        for edges in reps[n]:
            cnt += 1
            D = D_of(n, edges)
            Delta = max_delta(n, edges)
            L = (n - 1).bit_length()  # ceil(log2 n) for n>=1... check: n=2 -> 1? (1).bit_length()=1 ✓; n=9 -> 4? (8).bit_length()=4 ✓; n=8 -> (7).bit_length()=3 ✓
            twomax = 2 * max(Delta, L)
            if D >= twomax:
                risk += 1
                k = D // 2
                found = has_cf_coloring(n, edges, k)
                rec = {"n": n, "edges": [list(e) for e in edges],
                       "canon": canon(n, edges), "D": D, "Delta": Delta, "L": L,
                       "k_search": k, "cf_coloring_with_k_exists": found}
                out["risk_trees"].append(rec)
                if found:
                    out["violators_D_lt_2max"]  # placeholder; real counterexample:
                    out.setdefault("COUNTEREXAMPLES", []).append(rec)
            else:
                ok_trivial += 1
                slack = twomax - D
                if worst is None or slack < worst[0]:
                    worst = (slack, n, D, Delta, L, canon(n, edges))
            # pattern check D <= Delta + L - 1
        out["per_n"][n] = {"unlabeled": cnt, "risk": risk, "trivial_ok": ok_trivial}
        total += cnt
        print(f"n={n}: {cnt} trees, risk={risk}", flush=True)
    # source claim checks
    checks = {}
    # paths
    def path_edges(n):
        return tuple((i, i + 1) for i in range(n - 1))
    checks["D(P_n)=ceil(log2 n)"] = all(
        D_of(n, path_edges(n)) == (n - 1).bit_length() for n in range(2, min(N, 15) + 1))
    def star_edges(n):
        return tuple((0, i + 1) for i in range(n - 1))
    checks["D(K_{1,n-1})=n-1"] = all(
        D_of(n, star_edges(n)) == n - 1 for n in range(2, min(N, 15) + 1))
    # double star S_{a,b}: centers 0,1; a-1 leaves on 0, b-1 leaves on 1
    def dstar(a, b):
        e = [(0, 1)]
        nxt = 2
        for i in range(a - 1):
            e.append((0, nxt)); nxt += 1
        for i in range(b - 1):
            e.append((1, nxt)); nxt += 1
        return tuple(e), a + b
    ok = True
    for a in range(2, 7):
        for b in range(2, 7):
            e, n = dstar(a, b)
            if D_of(n, e) != max(a, b):
                ok = False
    checks["d(S_{a,b})=Delta"] = ok
    # binomial tree B_k: 2^{k-1} vertices
    def binom(k):
        if k == 1:
            return ([], 1)
        ea, na = binom(k - 1)
        eb, nb = binom(k - 1)
        e = list(ea) + [(a + na, b + na) for a, b in eb] + [(0, na)]
        return (e, na + nb)
    ok = True
    for k in range(2, 6):
        e, n = binom(k)
        if D_of(n, tuple(e)) != k - 1:
            ok = False
    checks["d(B_k)=k-1 (k<=5)"] = ok
    out["source_claim_checks"] = checks
    out["min_slack_2max_minus_D"] = worst
    out["total_trees"] = total
    out["memo_size"] = len(memo_D)
    print(json.dumps({k: out[k] for k in ["source_claim_checks", "min_slack_2max_minus_D", "total_trees", "memo_size"]}, indent=1))
    print("risk trees:", json.dumps(out["risk_trees"], indent=1)[:3000])
    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
    os.makedirs(W, exist_ok=True)
    with open(os.path.join(W, "scan-trees.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", datetime.datetime.now(datetime.timezone.utc).isoformat())

if __name__ == "__main__":
    main()
