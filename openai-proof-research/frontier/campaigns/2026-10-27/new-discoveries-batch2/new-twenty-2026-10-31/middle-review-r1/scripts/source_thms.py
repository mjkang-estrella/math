"""Check the source's proved statements on all connected graphs of order 2..7 (own code), and
record where G8 sits relative to each.  Statements (arXiv:2206.15439v1):
  Thm 2.1 (Cyman): ocd(G) <= n - delta(G), G connected.
  Thm 4.1: ceil(n/2) <= ocd(M(G)) <= n, G connected, n >= 2.
  Cor 4.2: ocd(M(G)) >= rho(G) (edge cover number), no isolated vertex.
  Thm 4.3: ocd(M(T)) = n for trees.   Thm 4.7: n >= 4, ocd(M(G)) = n iff G is a tree.
  Thm 4.12: ocd(M(K_{n1,n2})) = n2 for n2 >= n1 >= 2.   Remark 5.8: ocd(M(C4+K2)) = 3, ocd(M(C4+K3)) = 4.
"""
import sys, json, time
sys.path.insert(0, "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/scripts")
from mocd import *
D = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/data/"
t0 = time.time()

def max_matching(n, adj):
    best = 0
    def rec(free, size):
        nonlocal best
        if free == 0:
            best = max(best, size)
            return
        low = free & -free
        a = low.bit_length() - 1
        rec(free & ~low, size)  # a unmatched
        nb = adj[a] & free & ~low
        while nb:
            lb = nb & -nb
            nb ^= lb
            rec(free & ~low & ~lb, size + 1)
    rec((1 << n) - 1, 0)
    return best

viol = {"2.1": [], "4.1": [], "4.2": [], "4.3": [], "4.7": []}
count = 0
for n in range(2, 8):
    for code in open(D + "all%d.txt" % n):
        adj = decode(n, int(code))
        if not is_connected_graph(n, adj):
            continue
        count += 1
        m = popcount(int(code))
        tree = (m == n - 1)
        g = ocd_bruteforce(adj, n, "B")
        delta = min(popcount(a) for a in adj)
        N, madj, E = middle(n, adj)
        mm = ocd_branch(madj, N, "B")
        rho = n - max_matching(n, adj)
        E_ = edges_of(n, adj)
        if not g <= n - delta: viol["2.1"].append((n, E_, g, delta))
        if not (-(-n // 2) <= mm <= n): viol["4.1"].append((n, E_, mm))
        if not mm >= rho: viol["4.2"].append((n, E_, mm, rho))
        if tree and mm != n: viol["4.3"].append((n, E_, mm))
        if n >= 4 and ((mm == n) != tree): viol["4.7"].append((n, E_, mm))

def join_C4_Kp(p):
    n = 4 + p
    E = [(0, 1), (1, 2), (2, 3), (3, 0)]
    E += [(a, b) for a in range(4, n) for b in range(a + 1, n)]
    E += [(a, b) for a in range(4) for b in range(4, n)]
    return n, from_edges(n, E)
rem58 = {}
for p in (2, 3):
    n, adj = join_C4_Kp(p)
    N, madj, E = middle(n, adj)
    rem58["C4+K%d" % p] = ocd_branch(madj, N, "B")
kb = {}
for a in range(2, 4):
    for b in range(a, 6):
        n = a + b
        adj = from_edges(n, [(i, a + j) for i in range(a) for j in range(b)])
        N, madj, E = middle(n, adj)
        kb["K%d,%d" % (a, b)] = {"computed": ocd_branch(madj, N, "B"), "Thm4.12": b}
print(json.dumps({"connected_graphs_checked": count, "violations": viol,
                  "remark_5_8": rem58, "thm_4_12": kb, "elapsed": round(time.time() - t0, 2)}, indent=1))
