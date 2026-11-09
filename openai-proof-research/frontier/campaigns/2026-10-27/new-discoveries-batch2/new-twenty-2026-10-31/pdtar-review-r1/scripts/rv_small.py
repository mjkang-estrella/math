"""Independent small-case check (gate D), lane pdtar-review-r1. Written from scratch.

For each target G in {K2, K_{1,2}, K_{1,3}, K_{2,2}, K_{1,4}, K_{2,3}, K_{1,5}, K_{2,4}, K_{3,3}}:
  scan ALL labeled graphs H on 2..6 vertices with no isolated vertices;
  (i)  H whose PD family is a vertex relabeling of G's  => PD-TAR(H) = PD-TAR(G) up to relabeling
       (trivially isomorphic); report whether every such H is isomorphic to G;
  (ii) H whose PD-TAR graph has the same colour-refinement invariant as G's but whose PD family
       is NOT a relabeling of G's: such H would need an exact TAR-isomorphism test (and would
       contradict Theorem t:main if isomorphic). Exact test by backtracking is run if any occur.
Also checks K_{2,t}(e) has the same PD family as K_{2,t} (t=2..4) and K3 vs K_{1,2}.
"""
import itertools, json, time

def edges_of(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]

def pc(x):
    return bin(x).count("1")

def closure(n, nb, S):
    if S == 0:
        return 0
    P = S
    for v in range(n):
        if (S >> v) & 1:
            P |= nb[v]
    while True:
        add = 0
        for v in range(n):
            if (P >> v) & 1:
                r = nb[v] & ~P
                if r and (r & (r - 1)) == 0:
                    add |= r
        if not add:
            return P
        P |= add

def fam(n, nb):
    full = (1 << n) - 1
    return sum(1 << S for S in range(1, full + 1) if closure(n, nb, S) == full)

def nb_from_edges(n, es):
    nb = [0] * n
    for i, j in es:
        nb[i] |= 1 << j; nb[j] |= 1 << i
    return nb

def Kst(s, t):
    return nb_from_edges(s + t, [(a, s + b) for a in range(s) for b in range(t)])

def tar_adj(n, F):
    V = [S for S in range(1 << n) if (F >> S) & 1]
    idx = {S: i for i, S in enumerate(V)}
    adj = [[idx[S ^ (1 << v)] for v in range(n) if (F >> (S ^ (1 << v))) & 1] for S in V]
    return adj

def refine_inv(adj, rounds=3):
    col = [len(a) for a in adj]
    for _ in range(rounds):
        sig = [(col[i], tuple(sorted(col[j] for j in adj[i]))) for i in range(len(adj))]
        keys = sorted(set(sig))
        m = {k: i for i, k in enumerate(keys)}
        col = [m[x] for x in sig]
        last = keys
    return (len(adj), tuple(sorted(sig)))

def iso_graphs(adj1, adj2):
    """exact isomorphism test by backtracking with refinement colours"""
    n = len(adj1)
    if n != len(adj2):
        return False
    def colours(adj):
        col = [len(a) for a in adj]
        for _ in range(4):
            sig = [(col[i], tuple(sorted(col[j] for j in adj[i]))) for i in range(len(adj))]
            col = sig
        return col
    c1 = colours(adj1); c2 = colours(adj2)
    if sorted(map(repr, c1)) != sorted(map(repr, c2)):
        return False
    s1 = [set(a) for a in adj1]; s2 = [set(a) for a in adj2]
    order = sorted(range(n), key=lambda i: -len(adj1[i]))
    mp = {}; used = set()
    def bt(k):
        if k == n:
            return True
        u = order[k]
        for v in range(n):
            if v in used or repr(c1[u]) != repr(c2[v]):
                continue
            if all((w in s1[u]) == (mp[w] in s2[v]) for w in mp):
                mp[u] = v; used.add(v)
                if bt(k + 1):
                    return True
                del mp[u]; used.discard(v)
        return False
    return bt(0)

def perm_family(n, F, p):
    out = 0
    for S in range(1 << n):
        if (F >> S) & 1:
            T = 0
            for v in range(n):
                if (S >> v) & 1:
                    T |= 1 << p[v]
            out |= 1 << T
    return out

def graph_iso(n, nb1, nb2):
    for p in itertools.permutations(range(n)):
        if all(((nb1[u] >> v) & 1) == ((nb2[p[u]] >> p[v]) & 1) for u in range(n) for v in range(n)):
            return True
    return False

def main():
    t0 = time.time()
    targets = {"K2": (1, 1), "K1,2": (1, 2), "K1,3": (1, 3), "K2,2": (2, 2), "K1,4": (1, 4),
               "K2,3": (2, 3), "K1,5": (1, 5), "K2,4": (2, 4), "K3,3": (3, 3)}
    # precompute all graphs without isolated vertices on 2..6 vertices
    data = {}
    for n in range(2, 7):
        E = edges_of(n)
        lst = []
        for g in range(1 << len(E)):
            nb = nb_from_edges(n, [E[e] for e in range(len(E)) if (g >> e) & 1])
            if any(x == 0 for x in nb):
                continue
            lst.append((g, nb, fam(n, nb)))
        data[n] = lst
        print(f"n={n}: {len(lst)} labeled graphs without isolated vertices, t={time.time()-t0:.1f}s", flush=True)
    invcache = {}
    def inv_of(n, F):
        k = (n, F)
        if k not in invcache:
            invcache[k] = refine_inv(tar_adj(n, F))
        return invcache[k]
    results = {}
    for name, (s, t) in targets.items():
        n = s + t
        G = Kst(s, t)
        FG = fam(n, G)
        orbit = {perm_family(n, FG, p) for p in itertools.permutations(range(n))}
        invG = inv_of(n, FG)
        same_family = []
        inv_match_other = 0
        exact_iso_other = 0
        for n2 in range(2, 7):
            for g, nb, F in data[n2]:
                if n2 == n and F in orbit:
                    same_family.append(nb)
                    continue
                if inv_of(n2, F) == invG:
                    inv_match_other += 1
                    if iso_graphs(tar_adj(n2, F), tar_adj(n, FG)):
                        exact_iso_other += 1
        noniso = [nb for nb in same_family if not graph_iso(n, nb, G)]
        # isomorphism classes among the non-isomorphic witnesses (by edge count)
        results[name] = {"order": n, "PD_TAR_order": pc(FG), "labeled_H_with_relabelled_family": len(same_family),
                         "of_which_not_isomorphic_to_G": len(noniso),
                         "witness_edgecounts": sorted({sum(pc(x) for x in nb) // 2 for nb in noniso}),
                         "invariant_matches_with_other_family": inv_match_other,
                         "exact_TAR_iso_with_other_family": exact_iso_other,
                         "unique": len(noniso) == 0 and exact_iso_other == 0}
        print(name, results[name], f"t={time.time()-t0:.1f}s", flush=True)
    # explicit source witnesses
    wit = {}
    for t in range(2, 5):
        n = 2 + t
        G = Kst(2, t)
        Ge = nb_from_edges(n, [(a, 2 + b) for a in range(2) for b in range(t)] + [(0, 1)])
        wit[f"K2,{t} vs K2,{t}(e)"] = fam(n, G) == fam(n, Ge)
    wit["K1,2 vs K3"] = fam(3, Kst(1, 2)) == fam(3, nb_from_edges(3, [(0, 1), (0, 2), (1, 2)]))
    print(json.dumps({"results": results, "source_witnesses_same_family": wit, "seconds": round(time.time() - t0, 1)}, indent=1))

main()
