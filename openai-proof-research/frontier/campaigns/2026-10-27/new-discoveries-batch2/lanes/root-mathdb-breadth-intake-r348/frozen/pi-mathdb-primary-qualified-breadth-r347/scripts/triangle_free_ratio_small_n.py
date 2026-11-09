#!/usr/bin/env python3
"""Exhaustive labeled triangle-free graphs on n <= N vertices:
compute alpha(G) / E|I| where I is a uniformly random independent set.

Supports the disposition of MathDB records 400775/400774 (Davies' Conjecture 1,
arXiv:1606.01043): alpha(G)/alpha_G(1) >= 4/3 for every triangle-free G.

Method: DFS over all 2^C(n,2) edge subsets, pruning any prefix containing a
triangle (pruning is sound: any supergraph of a triangle-containing prefix
still contains that triangle). At each leaf, exact computation via bitmask DP:
  i(S)  = #independent sets of G[S]           (S subset of V)
  a(S)  = independence number of G[S]
  E|I|  = sum_v i(G - N[v]) / i(G)
Uniform random independent set: P(v in I) = i(G-N[v])/i(G), so E|I| is exact.

Pinned: OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
"""
import sys, time, json

def enum_and_eval(n, deadline):
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    m = len(edges)
    N = 1 << n
    full = N - 1
    # adjacency bit for each edge as (u_bit, v_bit, union)
    eu = [1 << e[0] for e in edges]
    ev = [1 << e[1] for e in edges]
    eab = [eu[k] | ev[k] for k in range(m)]

    best = []  # (ratio, graph_edges_bits, alpha, E)
    count = 0

    def eval_graph(adj):
        # i(S), a(S) via DP over masks, lowest vertex of S as pivot
        idp = [0] * N
        adp = [0] * N
        idp[0] = 1
        # a(0) = 0
        for S in range(1, N):
            v = (S & -S).bit_length() - 1
            S1 = S & ~(1 << v)
            S2 = S1 & ~adj[v]
            idp[S] = idp[S1] + idp[S2]
            a1 = adp[S1]
            a2 = adp[S2] + 1
            adp[S] = a1 if a1 > a2 else a2
        iG = idp[full]
        aG = adp[full]
        E = 0.0
        for v in range(n):
            E += idp[full & ~adj[v] & ~(1 << v)] / iG
        return aG, E, iG

    adj = [0] * n
    stack = [(0, 0)]  # (edge index, added-mask not needed; adj mutated w/ undo)
    idx = 0
    # iterative DFS with explicit stack of (edge_index, action)
    # simpler: recursion with undo
    sys.setrecursionlimit(10000)

    def dfs(k):
        nonlocal count
        if k == m:
            count += 1
            aG, E, iG = eval_graph(adj)
            if E > 0:
                r = aG / E
                if len(best) < 12:
                    best.append((r, tuple(adj), aG, E))
                    best.sort(key=lambda t: t[0])
                elif r < best[-1][0]:
                    best[-1] = (r, tuple(adj), aG, E)
                    best.sort(key=lambda t: t[0])
            return
        # prune: adding edge (x,y) must not create a triangle,
        # i.e. x and y must have no common neighbor
        x = edges[k][0]; y = edges[k][1]
        if not (adj[x] & adj[y]):
            adj[x] |= 1 << y
            adj[y] |= 1 << x
            dfs(k + 1)
            adj[x] &= ~(1 << y)
            adj[y] &= ~(1 << x)
        dfs(k + 1)

    t0 = time.time()
    dfs(0)
    return count, best, time.time() - t0

def main():
    out = {}
    for n in range(2, 8):
        count, best, dt = enum_and_eval(n, None)
        ratios = [b[0] for b in best]
        out[n] = {
            "triangle_free_graphs": count,
            "seconds": round(dt, 2),
            "min_ratio": ratios[0] if ratios else None,
            "min_ratio_graphs": [
                {"alpha": b[2], "E": round(b[3], 6), "ratio": round(b[0], 6),
                 "adjacency_bitmasks": list(b[1])} for b in best[:6]
            ],
        }
        print(f"n={n}: {count} triangle-free graphs, {dt:.1f}s, min ratio {ratios[0]:.6f}")
    # sanity: C5 (n=5) and 3-edge matching (n=6)
    def eval_adj(adj):
        n = len(adj); N = 1 << n; full = N-1
        idp = [0]*N; adp=[0]*N; idp[0]=1
        for S in range(1, N):
            v = (S & -S).bit_length()-1
            S1 = S & ~(1<<v); S2 = S1 & ~adj[v]
            idp[S] = idp[S1]+idp[S2]
            a1 = adp[S1]; a2 = adp[S2]+1
            adp[S] = a1 if a1 > a2 else a2
        iG = idp[full]; aG = adp[full]
        E = sum(idp[full & ~adj[v] & ~(1<<v)]/iG for v in range(n))
        return aG, E
    adj = [0]*5
    for i in range(5):
        adj[i] |= 1 << ((i+1) % 5)
        adj[(i+1) % 5] |= 1 << i
    a, E = eval_adj(adj)
    print(f"sanity C5: alpha={a} E={E:.6f} ratio={a/E:.6f} (expect 2/(15/11)=1.466667)")
    adjm = [0]*6
    for i in range(3):
        adjm[2*i] |= 1 << (2*i+1); adjm[2*i+1] |= 1 << (2*i)
    a, E = eval_adj(adjm)
    print(f"sanity 3xK2: alpha={a} E={E:.6f} ratio={a/E:.6f} (expect 1.5)")
    out["note"] = ("DFS prunes any prefix containing a triangle (common-neighbor check), so the "
                   "enumeration is exactly all labeled triangle-free graphs. Ratio alpha(G)/E|I| "
                   "with I uniform random independent set, computed exactly by bitmask DP. "
                   "Finite evidence only; does NOT clear Davies' Conjecture 1 (arXiv:1606.01043) "
                   "whose smallest known ratio 1.43283 occurs on 36 vertices.")
    with open("work/triangle_free_ratio_small_n.out", "w") as f:
        json.dump({"description": "Exhaustive labeled triangle-free graphs n<=7; min alpha/E ratios; supports 400775/400774 disposition only as finite evidence",
                   "results": out}, f, indent=1)
    print("wrote work/triangle_free_ratio_small_n.out")

if __name__ == "__main__":
    main()
