# Check Example 3 of arXiv:2004.09810v2 per rooted tree: f = x1 + x2 x3, n = 4, root G1 with C1 = (1110).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gjpo import analyse, trees, run, canon_cyc
n = 4
f = lambda v: ((v >> 2) & 1) ^ (((v >> 1) & 1) & (v & 1))
succ, comp, cycles = analyse(n, f)
fmt = lambda v: format(v, '04b')
root = comp[0b1110]
T, _ = trees(cycles, comp, 10**6)
for r, E in T:
    if r != root: continue
    outs = {}
    for u in cycles[r]:
        b = run(n, succ, E, u); s = ''.join(map(str, b)); outs[fmt(u)] = (s, canon_cyc(b))
    print('labels', sorted(fmt(w) for w in E), {u: o[0] for u, o in outs.items()}, 'inequivalent', len({o[1] for o in outs.values()}))
