"""Exhaustive test of Conjecture 7.1 over all graphs of order 2..NMAX (own code).
Usage: search.py NMIN NMAX
For each isomorphism class G (from data/all{n}.txt) and each convention c in {A,B}:
  g = min OCD size of G (brute force over all subsets);
  then decide whether M(G) has an OCD set of size <= g (exact branching search, cap g).
A failure of the strict inequality is reported with g and the exact value of ocd(M(G))."""
import sys, json, time
sys.path.insert(0, "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/scripts")
from mocd import *
D = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/data/"
NMIN, NMAX = int(sys.argv[1]), int(sys.argv[2])
t0 = time.time()
summary = {}
fails = []
for n in range(NMIN, NMAX + 1):
    codes = [int(x) for x in open(D + "all%d.txt" % n)]
    st = {"graphs": len(codes), "connected": 0, "edgeless": 0,
          "fail_connected": {"A": 0, "B": 0}, "fail_disconnected": {"A": 0, "B": 0},
          "fail_disconnected_with_edge": {"A": 0, "B": 0},
          "undefined_G_B": 0, "undefined_M_B": 0,
          "ocdG_ge_halfn_connected": 0}
    for code in codes:
        adj = decode(n, code)
        conn = is_connected_graph(n, adj)
        m = popcount(code)
        st["connected"] += conn
        st["edgeless"] += (m == 0)
        N, madj, E = middle(n, adj)
        for conv in "AB":
            g = ocd_bruteforce(adj, n, conv)
            if conv == "A" and conn and g >= (n + 1) // 2:
                st["ocdG_ge_halfn_connected"] += 1
            if g is None:
                st["undefined_G_B"] += 1
                mm = ocd_branch(madj, N, conv)
                if mm is None:
                    st["undefined_M_B"] += 1
                fails.append({"n": n, "edges": edges_of(n, adj), "conv": conv, "connected": conn,
                              "ocd_G": None, "ocd_M": mm, "kind": "G has no OCD set under B"})
                if not conn:
                    st["fail_disconnected"][conv] += 1
                    if m > 0:
                        st["fail_disconnected_with_edge"][conv] += 1
                continue
            mm = ocd_branch(madj, N, conv, cap=g)
            if mm is not None:  # ocd(M) <= ocd(G): strict inequality fails
                exact = mm
                key = "fail_connected" if conn else "fail_disconnected"
                st[key][conv] += 1
                if not conn and m > 0:
                    st["fail_disconnected_with_edge"][conv] += 1
                fails.append({"n": n, "edges": edges_of(n, adj), "conv": conv, "connected": conn,
                              "ocd_G": g, "ocd_M": exact, "kind": "equality" if exact == g else "reverse"})
    st["elapsed_s"] = round(time.time() - t0, 2)
    summary[n] = st
    print(n, json.dumps(st), flush=True)
print("FAILURES")
for f in fails:
    print(json.dumps(f))
print(json.dumps({"summary": summary, "n_failures": len(fails)}))
