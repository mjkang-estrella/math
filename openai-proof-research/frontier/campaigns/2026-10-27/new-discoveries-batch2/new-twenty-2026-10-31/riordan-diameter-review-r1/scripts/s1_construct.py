"""s1: construction cross-checks and io-decomposability by DEFINITION (CJKM Def. 4.1) versus Thm 4.6 form."""
import sys, random, itertools
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1/scripts')
from rcore import *

def mat(adj):
    n = len(adj)
    return [[(adj[i] >> j) & 1 for j in range(n)] for i in range(n)]

# 1. CG_6 adjacency matrix printed in CJKM v2 Example 2.5 / Jung Fig. 1
printed_CG6 = [[0,1,1,0,1,0],[1,0,1,0,1,0],[1,1,0,1,1,1],[0,0,1,0,1,0],[1,1,1,1,0,1],[0,0,1,0,1,0]]
cg6 = riordan_graph([1]*5, 6)
print('CG6 matches printed matrix:', mat(cg6) == printed_CG6)

# 2. Jung Example 2.7: reverse relabelling of CG_8 equals G_8(1, z+z^2) with the printed matrix
printed_CGr8 = [[0,1,0,0,0,0,0,0],[1,0,1,1,0,0,0,0],[0,1,0,1,0,1,0,0],[0,1,1,0,1,1,1,1],
                [0,0,0,1,0,1,0,0],[0,0,1,1,1,0,1,1],[0,0,0,1,0,1,0,1],[0,0,0,1,0,1,1,0]]
cg8 = riordan_graph([1]*7, 8)
rev = [[mat(cg8)[7 - i][7 - j] for j in range(8)] for i in range(8)]
gr = riordan_graph_general(1, 0b110, 8)
print('reverse(CG8) == printed CGr8:', rev == printed_CGr8, '; G8(1,z+z^2) == printed:', mat(gr) == printed_CGr8)

# 3. recurrence construction == power-series construction
rng = random.Random(20261104)
bad = 0; cnt = 0
for n in range(2, 11):
    for bits in range(1 << max(0, n - 2)):
        a = [1] + [(bits >> t) & 1 for t in range(n - 2)]
        cnt += 1
        if riordan_graph(a, n) != riordan_graph_ps(a, n):
            bad += 1
for n in (16, 24, 32, 48, 64):
    for _ in range(60):
        a = [1] + [rng.randrange(2) for _ in range(n - 2)]
        cnt += 1
        if riordan_graph(a, n) != riordan_graph_ps(a, n):
            bad += 1
print('recurrence vs power series: checked', cnt, 'mismatches', bad)

# 4. io-decomposability by definition: <Ve> null and <Vo> ~= G_{ceil(n/2)}(g,f)
def iso_bruteforce(g1, g2):
    n = len(g1)
    if n != len(g2) or sorted(popc(x) for x in g1) != sorted(popc(x) for x in g2):
        return False
    d1 = [popc(x) for x in g1]; d2 = [popc(x) for x in g2]
    for perm in itertools.permutations(range(n)):
        if any(d1[v] != d2[perm[v]] for v in range(n)):
            continue
        ok = True
        for v in range(n):
            m = 0
            for u in range(n):
                if (g1[v] >> u) & 1:
                    m |= 1 << perm[u]
            if m != g2[perm[v]]:
                ok = False; break
        if ok:
            return True
    return False

for n in (4, 6, 8, 10, 12, 16):
    stats = dict(total=0, form=0, def_labelled=0, def_unlabelled=0, form_not_def=0, def_not_form=0, def_unl_not_form=0)
    for bits in range(1 << (n - 2)):
        a = [1] + [(bits >> t) & 1 for t in range(n - 2)]
        stats['total'] += 1
        G = riordan_graph(a, n)
        odd = list(range(0, n, 2)); even = list(range(1, n, 2))
        Ve = induced(G, even)
        Vo = induced(G, odd)
        H = riordan_graph(a, (n + 1) // 2)
        nullVe = all(x == 0 for x in Ve)
        lab = nullVe and Vo == H
        form = is_io_form(a)
        unl = lab
        if nullVe and not lab and (n + 1) // 2 <= 8:
            unl = iso_bruteforce(Vo, H)
        stats['form'] += form
        stats['def_labelled'] += lab
        stats['def_unlabelled'] += unl
        stats['form_not_def'] += form and not lab
        stats['def_not_form'] += lab and not form
        stats['def_unl_not_form'] += unl and not form
    print('n =', n, stats)
