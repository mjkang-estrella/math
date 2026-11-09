# Z_n-equivariant total colouring of L(K_n), n odd (and n even via Z_{n-1} ∪ {inf}).
# Colours: orbit colours Z_m (m = n or n-1) and fixed colours 0..F-1, F = 2n-3-m.
# Vertex colour phi({i,j}) = (i+j)/2 (n odd); for n even: phi({i,j})=(i+j)/2 mod m, phi({i,inf})=i.
# Cherry (c; c+a, c+b) gets colour c + g({a,b}) (orbit) or fixed F({a,b}); centre inf handled separately.
import sys, itertools, subprocess, pathlib, json
n = int(sys.argv[1]); TL = sys.argv[2] if len(sys.argv) > 2 else '100'
odd = n % 2 == 1
m = n if odd else n - 1; F = 2*n - 3 - m; h = pow(2, -1, m)
INF = 'I'
pts = list(range(m)) + ([] if odd else [INF])
def add(x, s): return x if x == INF else (x + s) % m
def phi(x, y):
    if x == INF: return ('o', y)
    if y == INF: return ('o', x)
    return ('o', ((x + y) * h) % m)
def norm(c, ends):
    # orbit representative of cherry (c; ends) : shift so centre is 0 (or centre inf, shift so min finite end... )
    if c != INF:
        s = c; e = tuple(sorted((add(x, -s) for x in ends), key=str)); return ('f', e), s
    # centre inf: ends both finite: (inf; a, b) -> shift so that a=0 : class by difference
    a, b = ends; d1 = (b - a) % m; d2 = (a - b) % m
    if d1 <= d2: return ('i', d1), a
    return ('i', d2), b
classes = {}
cherries = []
for c in pts:
    for e in itertools.combinations([x for x in pts if x != c], 2):
        cl, s = norm(c, e); classes.setdefault(cl, len(classes)); cherries.append((c, e, cl, s))
nv = 0; X = {}; Y = {}
for cl in classes:
    for k in range(m): nv += 1; X[(cl, k)] = nv
    for f in range(F): nv += 1; Y[(cl, f)] = nv
cls = []
for cl in classes:
    lits = [X[(cl, k)] for k in range(m)] + [Y[(cl, f)] for f in range(F)]
    cls.append(lits)
    for a, b in itertools.combinations(lits, 2): cls.append([-a, -b])
def tvert(x, y): return tuple(sorted((x, y), key=str))
inc = {}
for (c, e, cl, s) in cherries:
    for x in e: inc.setdefault(tvert(c, x), []).append((cl, s))
for tv, items in inc.items():
    pv = phi(*tv)[1]
    for (cl, s) in items:
        cls.append([-X[(cl, (pv - s) % m)]])
    for (c1, s1), (c2, s2) in itertools.combinations(items, 2):
        for k in range(m): cls.append([-X[(c1, k)], -X[(c2, (k + s1 - s2) % m)]])
        for f in range(F):
            if c1 == c2: cls.append([-Y[(c1, f)]])
            else: cls.append([-Y[(c1, f)], -Y[(c2, f)]])
D = pathlib.Path(__file__).resolve().parents[2] / 'outputs' / 'cnf'; D.mkdir(parents=True, exist_ok=True); cnf = D / f'zn{n}.cnf'
with open(cnf, 'w') as fh:
    fh.write(f'p cnf {nv} {len(cls)}\n')
    for c in cls: fh.write(' '.join(map(str, c)) + ' 0\n')
cad = '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
res = subprocess.run([cad, '-q', '-t', TL, str(cnf)], capture_output=True, text=True)
st = [l for l in res.stdout.splitlines() if l.startswith('s ')]
out = {'n': n, 'classes': len(classes), 'vars': nv, 'clauses': len(cls), 'status': st}
if st and st[0] == 's SATISFIABLE':
    lits = set(int(t) for l in res.stdout.splitlines() if l.startswith('v ') for t in l[2:].split())
    g = {}
    for cl in classes:
        ks = [('o', k) for k in range(m) if X[(cl, k)] in lits] + [('x', f) for f in range(F) if Y[(cl, f)] in lits]
        g[cl] = ks[0]
    # build full colouring and verify independently
    col = {}
    for x, y in itertools.combinations(pts, 2): col[('v', tvert(x, y))] = phi(x, y)
    for (c, e, cl, s) in cherries:
        t = g[cl]; col[('c', c, e)] = ('o', (t[1] + s) % m) if t[0] == 'o' else t
    bad = 0
    for (c, e, cl, s) in cherries:
        for x in e:
            if col[('c', c, e)] == col[('v', tvert(c, x))]: bad += 1
    vs = list(itertools.combinations(pts, 2))
    for p, q in itertools.combinations(vs, 2):
        if set(p) & set(q) and col[('v', tvert(*p))] == col[('v', tvert(*q))]: bad += 1
    for tv in inc:
        a, b = tv
        cs = [col[('c', c, e)] for (c, e, cl, s) in cherries if tvert(c, e[0]) == tv or tvert(c, e[1]) == tv]
        if len(cs) != 2*n - 4 or len(set(cs)) != len(cs): bad += 1
    out['palette'] = len(set(col.values())); out['violations'] = bad
    out['g'] = {str(k): v for k, v in sorted(g.items(), key=lambda kv: str(kv[0]))}
print(json.dumps(out))
