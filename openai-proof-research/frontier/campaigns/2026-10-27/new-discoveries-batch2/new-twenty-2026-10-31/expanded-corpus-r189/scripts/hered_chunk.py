"""Chunked level-n search (minimal forbidden graphs only) for MathDB 333144.
usage: hered_chunk.py STATEDIR N START END  -> STATEDIR/l<N>-forb-<START>-<END>.json"""
import sys, json, pathlib, time
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from hered import Store, delete, gamma, gamma_e
S = pathlib.Path(sys.argv[1]); n, a, b = map(int, sys.argv[2:5])
prevm = json.loads((S / f'level-{n-1}.json').read_text())['members']
prev = Store()
for g in prevm: prev.add(list(g), n - 1)
cand = Store(); forb = []; nm = 0; t0 = time.time()
for h in prevm[a:b]:
    for S_ in range(1 << (n - 1)):
        adj = [h[u] | (((S_ >> u) & 1) << (n - 1)) for u in range(n - 1)] + [S_]
        if not cand.add(adj, n): continue
        if any(prev.find(delete(adj, n, v), n - 1) is None for v in range(n - 1)): continue
        g = gamma(adj, n); ge = gamma_e(adj, n, g)
        if ge == g: nm += 1
        else: forb.append(adj)
(S / f'l{n}-forb-{a}-{b}.json').write_text(json.dumps({'members_found_in_chunk_with_dups_across_chunks': nm, 'minimal_forbidden': forb}))
print('chunk', a, b, 'members(chunk-local)', nm, 'forbidden(chunk-local)', len(forb), 'elapsed', round(time.time() - t0, 1))
