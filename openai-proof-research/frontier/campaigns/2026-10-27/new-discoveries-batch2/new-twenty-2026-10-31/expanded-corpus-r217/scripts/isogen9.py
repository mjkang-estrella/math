# chunked generation of graphs of order n from all graphs of order n-1 (file of all graphs order n-1, any components)
# usage: isogen9.py chunk PARENTFILE OUTFILE START END   (parents = all graphs of order n-1, JSON lines [n,adj])
#        isogen9.py merge OUTFILE IN1 IN2 ...           (dedupe by canonical code; keep only min component >= 3)
#        isogen9.py parents OUTFILE N                    (write all graphs of order N via isogame.gen levels)
import sys, json
sys.path.insert(0, sys.argv[-1]) if False else None
import importlib.util, pathlib
spec = importlib.util.spec_from_file_location('isogame', str(pathlib.Path(sys.argv[0]).resolve().parent / 'isogame.py'))
isogame = importlib.util.module_from_spec(spec); spec.loader.exec_module(isogame)
mode = sys.argv[1]
if mode == 'parents':
    N = int(sys.argv[3])
    levels = {1: {isogame.canon(1, [0]): [0]}}
    for n in range(2, N + 1):
        cur = {}
        for g in levels[n - 1].values():
            for m in range(1 << (n - 1)):
                adj = [g[v] | ((m >> v & 1) << (n - 1)) for v in range(n - 1)] + [m]
                c = isogame.canon(n, adj)
                if c not in cur: cur[c] = adj
        levels[n] = cur
    with open(sys.argv[2], 'w') as f:
        for adj in levels[N].values(): f.write(json.dumps([N, adj]) + '\n')
    print('parents', N, len(levels[N]))
elif mode == 'chunk':
    lines = open(sys.argv[2]).read().splitlines()
    a, b = int(sys.argv[4]), int(sys.argv[5]); cur = {}
    for line in lines[a:b]:
        n0, g = json.loads(line); n = n0 + 1
        for m in range(1, 1 << n0):
            adj = [g[v] | ((m >> v & 1) << (n - 1)) for v in range(n - 1)] + [m]
            if not isogame.components_ok(n, adj): continue
            c = isogame.canon(n, adj)
            if c not in cur: cur[c] = adj
    with open(sys.argv[3], 'w') as f:
        for c, adj in cur.items(): f.write(json.dumps([str(c), n, adj]) + '\n')
    print('chunk', a, b, 'candidates', len(cur))
elif mode == 'merge':
    cur = {}
    for fn in sys.argv[3:]:
        for line in open(fn):
            c, n, adj = json.loads(line)
            if c not in cur: cur[c] = (n, adj)
    with open(sys.argv[2], 'w') as f:
        for n, adj in cur.values(): f.write(json.dumps([n, adj]) + '\n')
    print('merged', len(cur))
