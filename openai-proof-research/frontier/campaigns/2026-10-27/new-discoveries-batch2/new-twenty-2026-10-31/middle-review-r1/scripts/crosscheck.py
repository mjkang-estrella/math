"""Cross-validation, matching characterisation and the G_{a,b} family (own code).
Usage: crosscheck.py PART   with PART in {xval, lemma, family}"""
import sys, json, time
sys.path.insert(0, "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/scripts")
from mocd import *
D = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/data/"
part = sys.argv[1]
t0 = time.time()
G8E = [(0, 1), (0, 6), (1, 6), (2, 3), (2, 7), (3, 7), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
FOUND = [(0, 4), (0, 6), (1, 5), (1, 7), (2, 6), (2, 7), (3, 6), (3, 7), (4, 6), (5, 7), (6, 7)]

if part == "xval":
    # (1) exact branching value of ocd(M(G)) equals plain brute force over all subsets of M(G)
    rows = 0
    bad = []
    for n in range(2, 7):
        for code in open(D + "all%d.txt" % n):
            adj = decode(n, int(code))
            N, madj, E = middle(n, adj)
            if N > 16:
                continue
            for conv in "AB":
                a = ocd_branch(madj, N, conv)
                b = ocd_bruteforce(madj, N, conv)
                rows += 1
                if a != b:
                    bad.append((n, edges_of(n, adj), conv, a, b))
    print(json.dumps({"xval_rows": rows, "mismatches": bad}))
    # (2) the graph found at n = 8 is isomorphic to G8
    a1 = from_edges(8, G8E)
    a2 = from_edges(8, FOUND)
    i1, c1 = wl_invariant(8, a1)
    i2, c2 = wl_invariant(8, a2)
    print(json.dumps({"found_iso_G8": i1 == i2 and isomorphic(8, a1, c1, a2, c2)}))
    # (3) n = 8 connected graphs with ocd(G) >= 4: distribution of ocd(M) - ocd(G) (min gap)
    gaps = {}
    for code in open(D + "all8.txt"):
        adj = decode(8, int(code))
        if not is_connected_graph(8, adj):
            continue
        g = ocd_bruteforce(adj, 8, "B")
        if g < 4:
            continue
        N, madj, E = middle(8, adj)
        m = ocd_branch(madj, N, "B", cap=g + 1)
        key = "gap0" if m == g else ("gap1" if m == g + 1 else "gap>=2")
        gaps[key] = gaps.get(key, 0) + 1
    print(json.dumps({"n8_conn_ocdG_ge4_gap_distribution": gaps, "elapsed": round(time.time() - t0, 2)}))

elif part == "lemma":
    # For even n <= 8, connected G: ocd(M(G)) == n/2  <=>  G has a perfect matching F with G - F connected.
    res = {}
    viol = []
    for n in (2, 4, 6, 8):
        cnt = {"graphs": 0, "both": 0, "neither": 0}
        for code in open(D + "all%d.txt" % n):
            adj = decode(n, int(code))
            if not is_connected_graph(n, adj):
                continue
            cnt["graphs"] += 1
            N, madj, E = middle(n, adj)
            lhs = exists_ocd_of_size(madj, N, n // 2, "B") is not None
            # also no smaller OCD set exists (so ocd(M) == n/2 exactly when lhs)
            smaller = any(exists_ocd_of_size(madj, N, t, "B") is not None for t in range(n // 2))
            rhs = any(is_connected_graph(n, remove_edges(n, adj, F)) for F in perfect_matchings(n, adj))
            if smaller or lhs != rhs:
                viol.append((n, edges_of(n, adj), lhs, rhs, smaller))
            cnt["both" if lhs and rhs else "neither"] += 1
        res[n] = cnt
    print(json.dumps({"lemma_counts": res, "violations": viol, "elapsed": round(time.time() - t0, 2)}))

elif part == "family":
    def Gab(a, b):
        # x=0, y=1, t=2, u=3, then a triangles at x and b triangles at y
        E = [(0, 1), (2, 0), (2, 1), (3, 0), (3, 1)]
        v = 4
        F = [(2, 0), (3, 1)]
        for _ in range(a):
            E += [(0, v), (0, v + 1), (v, v + 1)]
            F.append((v, v + 1))
            v += 2
        for _ in range(b):
            E += [(1, v), (1, v + 1), (v, v + 1)]
            F.append((v, v + 1))
            v += 2
        return v, E, F
    rows = []
    for a in range(1, 4):
        for b in range(a, 4):
            n, E, F = Gab(a, b)
            adj = from_edges(n, E)
            g = ocd_bruteforce(adj, n, "B")
            N, madj, EE = middle(n, adj)
            Dm = 0
            for (p, q) in F:
                Dm |= 1 << (n + EE.index((min(p, q), max(p, q))))
            dom_ok = is_ocd(madj, N, Dm, "B")
            pm_ok = sorted(v for e in F for v in e) == list(range(n))
            rem_conn = is_connected_graph(n, remove_edges(n, adj, F))
            row = {"a": a, "b": b, "n": n, "m": len(E), "ocd_G": g, "half_n": n // 2,
                   "matching_D_is_ocd_of_M": dom_ok, "F_perfect": pm_ok, "G_minus_F_connected": rem_conn}
            if N <= 26:  # exact value of ocd(M) by branching for the smaller members
                row["ocd_M_exact"] = ocd_branch(madj, N, "B")
            rows.append(row)
            print(json.dumps(row), flush=True)
    # G8 is G_{1,1}
    n, E, F = Gab(1, 1)
    a1 = from_edges(8, G8E)
    a2 = from_edges(n, E)
    i1, c1 = wl_invariant(8, a1)
    i2, c2 = wl_invariant(8, a2)
    print(json.dumps({"G11_iso_G8": i1 == i2 and isomorphic(8, a1, c1, a2, c2), "elapsed": round(time.time() - t0, 2)}))
