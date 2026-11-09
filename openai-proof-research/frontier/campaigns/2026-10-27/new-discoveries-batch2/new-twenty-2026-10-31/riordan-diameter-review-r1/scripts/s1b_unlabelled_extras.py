"""s1b: the extra finite graphs that satisfy CJKM Def. 4.1 only under an UNLABELLED reading of '~=':
   list them for n = 8 and n = 16 with diameters (sensitivity check of the class definition)."""
import sys, itertools
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1/scripts')
from rcore import *

def iso_bruteforce(g1, g2):
    n = len(g1)
    d1 = [popc(x) for x in g1]; d2 = [popc(x) for x in g2]
    if sorted(d1) != sorted(d2):
        return False
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

for n, k in ((8, 3), (16, 4)):
    hist = {}
    examples = []
    for bits in range(1 << (n - 2)):
        a = [1] + [(bits >> t) & 1 for t in range(n - 2)]
        if is_io_form(a):
            continue
        G = riordan_graph(a, n)
        if any(induced(G, list(range(1, n, 2)))):
            continue
        Vo = induced(G, list(range(0, n, 2)))
        H = riordan_graph(a, n // 2)
        if Vo == H or not iso_bruteforce(Vo, H):
            continue
        d = diameter(G)
        hist[d] = hist.get(d, 0) + 1
        if len(examples) < 3 or d == k:
            examples.append((''.join(map(str, a)), d, edges(G)))
    print('n =', n, 'unlabelled-only extras: diameter histogram', dict(sorted(hist.items(), key=lambda t: (t[0] is None, t[0] or 0))))
    for e in examples[:12]:
        print('   example A-prefix', e[0], 'diam', e[1], 'edges', e[2])
