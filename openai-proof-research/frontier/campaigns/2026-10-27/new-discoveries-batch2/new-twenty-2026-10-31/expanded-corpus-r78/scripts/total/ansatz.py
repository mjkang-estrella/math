# Equivariant total colouring of L(K_n) with 2n-3 colours.
# V(K_n) = Z_r ∪ {A,B}, r = n-2. Colours: (t, s) t in Z_r, s in {0,1}, plus '*'. Group Z_r acts by translation.
import sys, itertools, subprocess, pathlib, json
n = int(sys.argv[1]); r = n - 2
pts = list(range(r)) + ['A', 'B']
def sh(x, g): return x if isinstance(x, str) else (x + g) % r
def key2(a, b): return tuple(sorted((a, b), key=str))
V = [key2(a, b) for a, b in itertools.combinations(pts, 2)]
# elements: ('v', pair) and ('c', centre, frozenset ends)
E = []
for c in pts:
    others = [x for x in pts if x != c]
    for x, y in itertools.combinations(others, 2):
        E.append(('c', c, key2(x, y)))
elems = [('v', p) for p in V] + E
idx = {el: i for i, el in enumerate(elems)}
cols = [(t, s) for t in range(r) for s in (0, 1)] + ['*']
cidx = {c: i for i, c in enumerate(cols)}; K = len(cols); assert K == 2*n - 3
def act(el, g):
    if el[0] == 'v': return ('v', key2(sh(el[1][0], g), sh(el[1][1], g)))
    return ('c', sh(el[1], g), key2(sh(el[2][0], g), sh(el[2][1], g)))
def cact(c, g): return c if c == '*' else ((c[0] + g) % r, c[1])
var = lambda i, c: i*K + c + 1
cls = [[var(i, c) for c in range(K)] for i in range(len(elems))]
conf = set()
def vert(p): return idx[('v', p)]
for (c, ends) in [(e[1], e[2]) for e in E]:
    x, y = ends; ei = idx[('c', c, ends)]
    conf.add((vert(key2(c, x)), vert(key2(c, y))))
    conf.add((vert(key2(c, x)), ei)); conf.add((vert(key2(c, y)), ei))
# edges of L incident to vertex p={a,b}: cherries centred a containing b, centred b containing a
for p in V:
    a, b = p; inc = []
    for e in E:
        if (e[1] == a and b in e[2]) or (e[1] == b and a in e[2]): inc.append(idx[e])
    for i, j in itertools.combinations(inc, 2): conf.add((i, j))
for i, j in conf:
    for c in range(K): cls.append([-var(i, c), -var(j, c)])
for i, el in enumerate(elems):
    j = idx[act(el, 1)]
    for c in range(K):
        cls.append([-var(i, c), var(j, cidx[cact(cols[c], 1)])])
D = pathlib.Path(__file__).resolve().parents[2] / 'outputs' / 'cnf'; D.mkdir(parents=True, exist_ok=True); cnf = D / f'ans{n}.cnf'
with open(cnf, 'w') as f:
    f.write(f'p cnf {len(elems)*K} {len(cls)}\n')
    for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
cad = '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
res = subprocess.run([cad, '-q', '-t', '100', str(cnf)], capture_output=True, text=True)
st = [l for l in res.stdout.splitlines() if l.startswith('s ')]
out = {'n': n, 'status': st}
if st and st[0] == 's SATISFIABLE':
    lits = set(int(t) for l in res.stdout.splitlines() if l.startswith('v ') for t in l[2:].split())
    col = {el: cols[[c for c in range(K) if var(i, c) in lits][0]] for el, i in idx.items()}
    out['ok'] = all(col[elems[i]] != col[elems[j]] for i, j in conf)
    reps = {}
    for el, c in col.items():
        if el[0] == 'v' and (0 in el[1] or el[1] == ('A', 'B')): reps[str(el)] = c
        if el[0] == 'c' and el[1] in (0, 'A', 'B'): reps[str(el)] = c
    out['reps'] = reps
print(json.dumps(out, default=str))
