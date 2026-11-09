"""G8 witness and source-family sanity checks (own code, python3 -I)."""
import sys, json
sys.path.insert(0, "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/scripts")
from mocd import *

out = {}
G8E = [(0, 1), (0, 6), (1, 6), (2, 3), (2, 7), (3, 7), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
n = 8
adj = from_edges(n, G8E)
out["G8_edges"] = G8E
out["G8_connected"] = is_connected_graph(n, adj)
out["G8_degrees"] = [popcount(a) for a in adj]
for conv in "AB":
    best, sets = all_min_ocd(adj, n, conv)
    out[f"G8_ocd_{conv}"] = best
    out[f"G8_min_sets_{conv}"] = [[v for v in range(n) if S >> v & 1] for S in sets]
N, madj, E = middle(n, adj)
out["M8_nodes"] = N
out["M8_edges_count"] = sum(popcount(a) for a in madj) // 2
out["M8_edge_index"] = {n + j: e for j, e in enumerate(E)}
for conv in "AB":
    out[f"M8_ocd_branch_{conv}"] = ocd_branch(madj, N, conv)
# brute force all subsets of size <= 4 of the 19 nodes (independent of branching code)
cnt = {}
mins = []
from itertools import combinations
for k in range(0, 5):
    c = 0
    for comb in combinations(range(N), k):
        S = 0
        for v in comb:
            S |= 1 << v
        if is_ocd(madj, N, S, "A"):
            c += 1
            if k == 4:
                mins.append([("v%d" % v) if v < n else "m%d%d" % E[v - n] for v in comb])
    cnt[k] = c
out["M8_bruteforce_ocd_counts_by_size_le4"] = cnt
out["M8_min_ocd_sets"] = mins
# dominating sets of M(G8) of size <= 3: should be none (counting bound)
dom3 = 0
full = (1 << N) - 1
for k in range(0, 4):
    for comb in combinations(range(N), k):
        S = 0
        for v in comb:
            S |= 1 << v
        if is_dominating(madj, S, full):
            dom3 += 1
out["M8_dominating_sets_size_le3"] = dom3
# certificate checks from PROOF.md
S0 = (1 << 0) | (1 << 2) | (1 << 4) | (1 << 5)
out["S0_is_ocd"] = is_ocd(adj, n, S0, "B")
D = 0
for e in [(0, 1), (2, 3), (4, 6), (5, 7)]:
    D |= 1 << (n + E.index(e))
out["D_matching_is_ocd"] = is_ocd(madj, N, D, "B")
# perfect matchings of G8 with connected remainder
pms = perfect_matchings(n, adj)
good = [F for F in pms if is_connected_graph(n, remove_edges(n, adj, F))]
out["G8_perfect_matchings"] = len(pms)
out["G8_pm_connected_remainder"] = good

# ---- source-family sanity checks (validate our reading of the definitions against the paper)
def K(n):
    return from_edges(n, [(a, b) for a in range(n) for b in range(a + 1, n)])
def C(n):
    return from_edges(n, [(i, (i + 1) % n) for i in range(n)])
def W(n):  # wheel of order n: hub 0, rim 1..n-1
    r = n - 1
    return from_edges(n, [(0, i) for i in range(1, n)] + [(i, i % r + 1) for i in range(1, n)])
def F(k):  # friendship graph F_k: 2k+1 vertices
    return from_edges(2 * k + 1, [(0, i) for i in range(1, 2 * k + 1)] + [(2 * i - 1, 2 * i) for i in range(1, k + 1)])
def Kb(a, b):
    return from_edges(a + b, [(i, a + j) for i in range(a) for j in range(b)])
def P(n):
    return from_edges(n, [(i, i + 1) for i in range(n - 1)])
def star(n):
    return from_edges(n, [(0, i) for i in range(1, n)])

fam = []
def rec(name, nn, a, expG=None, expM=None):
    g = ocd_bruteforce(a, nn, "B")
    Nm, ma, _ = middle(nn, a)
    m = ocd_branch(ma, Nm, "B")
    fam.append({"graph": name, "n": nn, "ocd_G": g, "ocd_M": m, "source_G": expG, "source_M": expM,
                "match": (expG is None or g == expG) and (expM is None or m == expM), "strict": g < m})
for k in range(3, 9):
    rec("K%d" % k, k, K(k), 1, -(-k // 2))
for k in range(3, 10):
    rec("C%d" % k, k, C(k), k - 2, k - 1)
for k in range(4, 10):
    rec("W%d" % k, k, W(k), 1, -(-k // 2))
for k in range(2, 4):
    rec("F%d" % k, 2 * k + 1, F(k), 1, k + 1)
for a in range(2, 4):
    for b in range(a, 5):
        if a + b <= 8:
            rec("K%d,%d" % (a, b), a + b, Kb(a, b), 2, b)
for k in range(2, 9):
    rec("P%d" % k, k, P(k), None, k)
for k in range(3, 9):
    rec("Star%d" % k, k, star(k), None, k)
out["source_family_checks"] = fam
out["all_source_values_match"] = all(r["match"] for r in fam)
print(json.dumps(out, indent=1))
