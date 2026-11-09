import sys, json, pathlib
D = pathlib.Path(sys.argv[1]).resolve()
sys.path.insert(0, str(D / 'scripts'))
import ncflow as N, snarklib as L

tests = []
n, E = L.petersen(); tests.append(('P10', n, E))
tests.append(('P10-triangle', *L.tri(n, E, 0)))
tests.append(('P10-digon', *L.digon_on(n, E, 0)))
tests.append(('P10-digon-spoke', *L.digon_on(n, E, 5)))
tests.append(('2sum(P10-e,P10-e)', *L.two_sum(n, E, 0, n, E, 0)))
tests.append(('2sum(P10-e,P10-spoke)', *L.two_sum(n, E, 0, n, E, 5)))
# dot products of two Petersens (Blanusa type), all independent edge pairs of P10 up to a few
seen = 0
for k1 in range(15):
    for k2 in range(k1 + 1, 15):
        if len(set(E[k1]) | set(E[k2])) == 4 and seen < 4:
            tests.append((f'dot(P10;{k1},{k2})', *L.dot(n, E, k1, k2, n, E, 0))); seen += 1
for k in (5, 7):
    tests.append((f'J{k}', *L.flower(k)))
which = sys.argv[2] if len(sys.argv) > 2 else None
for name, n2, E2 in tests:
    if which and which not in name: continue
    r = N.analyse(name, n2, E2, want_ham=n2 <= 22)
    r['three_edge_colourable'] = N.three_edge_colourable(n2, E2, N.adjacency(n2, E2)) if not r['has_nc_flow'] else 'not needed'
    w = r.pop('witness')
    print(json.dumps(r), flush=True)
    if w and len(sys.argv) > 3: print('  witness', json.dumps(w))
