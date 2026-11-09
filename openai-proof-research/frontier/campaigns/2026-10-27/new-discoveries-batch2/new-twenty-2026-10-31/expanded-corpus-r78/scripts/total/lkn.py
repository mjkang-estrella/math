# Total colouring of L(K_n) with 2n-3 colours as SAT (CNF for CaDiCaL).
# Elements: vertices of L(K_n) (= edges of K_n) and edges of L(K_n) (= pairs of K_n-edges sharing an endpoint).
# Conflicts: adjacent vertices; incident vertex-edge; edges sharing an L(K_n)-vertex.
import sys, itertools, subprocess, pathlib, json
n = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv) > 2 else 2*n-3
V = list(itertools.combinations(range(n), 2))
E = [(a, b) for a, b in itertools.combinations(V, 2) if set(a) & set(b)]
elems = [('v', x) for x in V] + [('e', e) for e in E]
idx = {el: i for i, el in enumerate(elems)}
var = lambda i, c: i*k + c + 1
cls = []
for i in range(len(elems)):
    cls.append([var(i, c) for c in range(k)])
conf = set()
for (a, b) in E:
    conf.add((idx[('v', a)], idx[('v', b)]))
    conf.add((idx[('v', a)], idx[('e', (a, b))])); conf.add((idx[('v', b)], idx[('e', (a, b))]))
inc = {x: [] for x in V}
for e in E:
    inc[e[0]].append(e); inc[e[1]].append(e)
for x in V:
    for e, f in itertools.combinations(inc[x], 2): conf.add((idx[('e', e)], idx[('e', f)]))
for (i, j) in conf:
    for c in range(k): cls.append([-var(i, c), -var(j, c)])
# symmetry breaking: colour the vertex (0,1) with 0 and its incident edges distinct fixed? keep simple: fix vertex 0 colour 0
cls.append([var(0, 0)])
D = pathlib.Path(sys.argv[3]); D.mkdir(parents=True, exist_ok=True)
cnf = D / f'lk{n}_k{k}.cnf'
with open(cnf, 'w') as f:
    f.write(f'p cnf {len(elems)*k} {len(cls)}\n')
    for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
cad = '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
r = subprocess.run([cad, '-q', '-t', '100', str(cnf)], capture_output=True, text=True)
status = [l for l in r.stdout.splitlines() if l.startswith('s ')]
sol = None
if status and 'SATISFIABLE' == status[0][2:]:
    lits = set(int(t) for l in r.stdout.splitlines() if l.startswith('v ') for t in l[2:].split())
    col = {}
    for el, i in idx.items():
        cs = [c for c in range(k) if var(i, c) in lits]; col[el] = cs[0]
    ok = all(col[elems[i]] != col[elems[j]] for i, j in conf)
    sol = ok
print(json.dumps({'n': n, 'colours': k, 'vertices': len(V), 'edges': len(E), 'clauses': len(cls), 'status': status, 'independently_checked': sol}))
