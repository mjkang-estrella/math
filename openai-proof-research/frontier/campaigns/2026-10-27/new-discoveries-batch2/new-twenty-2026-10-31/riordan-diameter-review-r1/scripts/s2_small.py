"""s2: exhaustive k = 1..4 (all io prefixes), (R1) failures at k = 2, 3, Jung Tables 1 and 2 recomputed."""
import sys, itertools
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1/scripts')
from rcore import *

def wl_hash(adj, rounds=4):
    n = len(adj)
    col = [popc(x) for x in adj]
    for _ in range(rounds):
        col = [hash((col[v], tuple(sorted(col[u] for u in range(n) if (adj[v] >> u) & 1)))) for v in range(n)]
    return tuple(sorted(col))

def iso_bruteforce(g1, g2):
    n = len(g1)
    d1 = [popc(x) for x in g1]; d2 = [popc(x) for x in g2]
    if sorted(d1) != sorted(d2):
        return False
    for perm in itertools.permutations(range(n)):
        if any(d1[v] != d2[perm[v]] for v in range(n)):
            continue
        if all(sum(1 << perm[u] for u in range(n) if (g1[v] >> u) & 1) == g2[perm[v]] for v in range(n)):
            return True
    return False

for k in (1, 2, 3, 4):
    N = 2 ** k
    CG = riordan_graph([1] * (N - 1), N)
    hist = {}
    diamk = []
    seqs = io_sequences(N - 1)
    for a in seqs:
        G = riordan_graph(a, N)
        d = diameter(G)
        hist[d] = hist.get(d, 0) + 1
        if d == k:
            diamk.append(a)
    print(f'k={k} N={N}: #io prefixes={len(seqs)} diam histogram={dict(sorted(hist.items()))} diam(CG)={diameter(CG)} edges(CG)={edges(CG)}')
    for a in diamk:
        G = riordan_graph(a, N)
        same = (G == CG)
        if same:
            iso = True
        elif N <= 8:
            iso = iso_bruteforce(G, CG)
        else:
            iso = (edges(G) == edges(CG) and wl_hash(G) == wl_hash(CG))  # necessary condition only
        print('   diam-k prefix', ''.join(map(str, a)), 'labelled==CG:', same, 'isomorphic to CG:', iso, 'edges', edges(G))

# explicit k = 2 and k = 3 counterexamples to (R1)
G4 = riordan_graph([1, 1, 0], 4)
E = sorted((j + 1, i + 1) for i in range(4) for j in range(i) if (G4[i] >> j) & 1)
print('G_4 with A=(1,1,0): edges', E, 'diam', diameter(G4))
G4c = riordan_graph([1, 1, 1], 4)
print('CG_4 edges', sorted((j + 1, i + 1) for i in range(4) for j in range(i) if (G4c[i] >> j) & 1), 'diam', diameter(G4c))
G8 = riordan_graph([1, 1, 1, 1, 1, 1, 0], 8)
C8 = riordan_graph([1] * 7, 8)
diff = sorted((j + 1, i + 1) for i in range(8) for j in range(i) if ((G8[i] ^ C8[i]) >> j) & 1)
print('G_8 with A=1111110 vs CG_8: symmetric difference of edge sets', diff, 'diam', diameter(G8), 'edges', edges(G8), 'vs', edges(C8))

# Jung Table 1 as printed (column-major reading of the rendered page)
printed_T1 = [('1100000', 2), ('1111000', 2), ('1100110', 2), ('1100001', 2), ('1111110', 2),
              ('1111001', 2), ('1100111', 2), ('1111110', 3), ('1111111', 3)]
print('Jung Table 1 check (printed -> recomputed):')
for s, d in printed_T1:
    a = [int(c) for c in s]
    print('   ', s, 'printed', d, 'recomputed', diameter(riordan_graph(a, 8)))
allio8 = {''.join(map(str, a)) for a in io_sequences(7)}
print('   io sequences for G_8 not printed in Table 1:', sorted(allio8 - {s for s, _ in printed_T1}))

# Jung Table 2: all io prefixes of length 15 with first 6 entries 1
printed_T2 = """111111000000000 3
111111001100000 3
111111000011000 3
111111000000110 3
111111000000001 3
111111001111000 3
111111001100110 3
111111001100001 3
111111000011110 3
111111000011001 3
111111001111110 3
111111001100111 3
111111001111001 3
111111001111110 3
111111001111111 3
111111110000000 3
111111111100000 3
111111110011000 3
111111110000110 3
111111110000001 3
111111111111000 3
111111111100110 3
111111111100001 3
111111110011110 3
111111110011001 3
111111110000111 3
111111111111110 3
111111111111001 3
111111111100111 3
111111110011111 3
111111111111111 4"""
rows = [(l.split()[0], int(l.split()[1])) for l in printed_T2.splitlines()]
mism = 0
for s, d in rows:
    rd = diameter(riordan_graph([int(c) for c in s], 16))
    if rd != d:
        mism += 1
        print('   Table 2 mismatch', s, d, rd)
allT2 = {''.join(map(str, a)) for a in io_sequences(15) if all(a[:6])}
printed = [s for s, _ in rows]
dups = sorted({s for s in printed if printed.count(s) > 1})
missing = sorted(allT2 - set(printed))
print('Jung Table 2: printed rows', len(rows), 'distinct', len(set(printed)), 'expected', len(allT2),
      'duplicates', dups, 'missing', missing, 'diameter mismatches', mism)
for s in missing:
    print('   missing row', s, 'recomputed diam', diameter(riordan_graph([int(c) for c in s], 16)))
