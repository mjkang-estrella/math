"""Diagnostic only (related MathDB 355218 = source Conjecture 7.6, ocd(L(G)) <= ocd(M(G))).
For all connected graphs of order 2..NMAX: does L(G) have an OCD set of size <= ocd(M(G))?
Also reports ocd(L(G8)).  Usage: conj76_probe.py NMAX"""
import sys, json, time
sys.path.insert(0, "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/scripts")
from mocd import *
D = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/data/"
NMAX = int(sys.argv[1])
t0 = time.time()

def line(n, adj):
    E = edges_of(n, adj)
    m = len(E)
    ladj = [0] * m
    for i in range(m):
        for j in range(i + 1, m):
            if set(E[i]) & set(E[j]):
                ladj[i] |= 1 << j
                ladj[j] |= 1 << i
    return m, ladj

G8E = [(0, 1), (0, 6), (1, 6), (2, 3), (2, 7), (3, 7), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
a8 = from_edges(8, G8E)
m8, l8 = line(8, a8)
print(json.dumps({"ocd_L_G8_A": ocd_branch(l8, m8, "A"), "ocd_L_G8_B": ocd_branch(l8, m8, "B")}))
viol = []
for n in range(2, NMAX + 1):
    cnt = 0
    for code in open(D + "all%d.txt" % n):
        adj = decode(n, int(code))
        if not is_connected_graph(n, adj):
            continue
        cnt += 1
        N, madj, E = middle(n, adj)
        for conv in "AB":
            mm = ocd_branch(madj, N, conv)
            m, ladj = line(n, adj)
            ll = ocd_branch(ladj, m, conv, cap=mm)
            if ll is None:
                viol.append({"n": n, "edges": edges_of(n, adj), "conv": conv, "ocd_M": mm,
                             "ocd_L": ocd_branch(ladj, m, conv)})
    print(n, cnt, len(viol), round(time.time() - t0, 2), flush=True)
print(json.dumps({"violations_of_7_6": viol}))
