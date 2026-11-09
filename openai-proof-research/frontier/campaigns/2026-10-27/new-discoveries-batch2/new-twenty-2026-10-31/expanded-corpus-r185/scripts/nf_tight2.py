"""Tight-list sweep for MathDB 344926 using nf_solver (exact, verified solutions).
Usage: nf_tight2.py v slack chunk nchunks
"""
import sys, itertools, time, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from nf_solver import make_solver, counts_of
v = int(sys.argv[1]); s = int(sys.argv[2]); ci = int(sys.argv[3]); nc = int(sys.argv[4])
n = (v - 1) // 2
divs = [d for d in range(3, v + 1) if v % d == 0]
lists = set()
for d in divs:
    bound = (v - d) // 2
    mult = [x for x in range(1, n + 1) if x % d == 0]
    non = [x for x in range(1, n + 1) if x % d != 0]
    if not mult: continue
    for m in range(max(0, bound - s), min(bound, n) + 1):
        for A in itertools.combinations_with_replacement(mult, m):
            for B in itertools.combinations_with_replacement(non, n - m):
                L = tuple(sorted(A + B))
                if all(sum(1 for x in L if x % dd == 0) <= (v - dd) // 2 for dd in divs): lists.add(L)
lists = sorted(lists)
solve = make_solver(v)
t0 = time.time(); checked = fails = 0; maxnodes = 0
for i, L in enumerate(lists):
    if i % nc != ci: continue
    sol, nodes = solve(counts_of(v, L)); checked += 1; maxnodes = max(maxnodes, nodes)
    if sol is None: fails += 1; print('FAIL', v, L, 'nodes', nodes, flush=True)
    else:
        assert sorted(l for _, _, l in sol) == list(L)
        assert sorted([a for a, b, l in sol] + [b for a, b, l in sol]) == list(range(1, v))
        assert all(min((a - b) % v, (b - a) % v) == l for a, b, l in sol)
    if time.time() - t0 > 85: print('TIME-STOP after list index', i, flush=True); break
print('v', v, 'slack', s, 'chunk', ci, '/', nc, 'tight total', len(lists), 'checked', checked, 'fails', fails, 'max nodes', maxnodes, 'secs', round(time.time() - t0, 1), flush=True)
