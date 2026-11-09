# Reduced SAT for total colouring of L(K_n) with 2n-3 colours.
# phi(ab) = class of ab in a (near-)1-factorization; cherry (a;b,x) default colour phi(bx);
# for each pair {e,f} of edges in the same class, choose orientation: e->f recolours cherries
# (p; f) for p in e with "extra" colours; extra colours must be distinct at each T-vertex.
# Final colouring is verified independently from scratch.
import sys, itertools, subprocess, pathlib, json
n = int(sys.argv[1]); cyc = len(sys.argv) > 2 and sys.argv[2] == 'cyc'
if n % 2 == 0:
    m = n - 1; pts = list(range(m)) + ['I']
    def phi(a, b):
        if a == 'I': return b
        if b == 'I': return a
        return ((a + b) * pow(2, -1, m)) % m
    ncls = m
else:
    m = n; pts = list(range(m))
    def phi(a, b): return ((a + b) * pow(2, -1, m)) % m   # near-1-factor c misses vertex c
    ncls = m
X = 2*n - 3 - ncls   # number of extra colours
pairs = [tuple(sorted(p, key=str)) for p in itertools.combinations(pts, 2)]
byc = {}
for p in pairs: byc.setdefault(phi(*p), []).append(p)
ori = {}  # (e,f) with e<f in same class -> var; True means e->f
nv = 0
def new():
    global nv; nv += 1; return nv
for c, es in byc.items():
    for e, f in itertools.combinations(es, 2): ori[(e, f)] = new()
cher = []  # (centre, (s,t))
for p in pts:
    for s, t in itertools.combinations([x for x in pts if x != p], 2): cher.append((p, tuple(sorted((s, t), key=str))))
y = {(ch, k): new() for ch in cher for k in range(X)}
rec = {ch: new() for ch in cher}  # recoloured indicator
cls = []
def edge_of(p, q): return tuple(sorted((p, q), key=str))
for ch in cher:
    p, f = ch; c = phi(*f)
    # cherry (p;f) recoloured iff orientation e->f where e = class-c edge at p (if exists and disjoint from f)
    es = [e for e in byc[c] if p in e]
    if not es or set(es[0]) & set(f):
        cls.append([-rec[ch]])  # no conflict partner -> cannot need recolouring? (handled by check)
    else:
        e = es[0]
        if (e, f) in ori: o = ori[(e, f)]; cls += [[-rec[ch], o], [rec[ch], -o]]
        else: o = ori[(f, e)]; cls += [[-rec[ch], -o], [rec[ch], o]]
    cls.append([-rec[ch]] + [y[(ch, k)] for k in range(X)])
    for k in range(X): cls.append([rec[ch], -y[(ch, k)]])
    for k1, k2 in itertools.combinations(range(X), 2): cls.append([-y[(ch, k1)], -y[(ch, k2)]])
inc = {p: [] for p in pairs}
for ch in cher:
    p, (s, t) = ch; inc[edge_of(p, s)].append(ch); inc[edge_of(p, t)].append(ch)
for p, chs in inc.items():
    for a, b in itertools.combinations(chs, 2):
        for k in range(X): cls.append([-y[(a, k)], -y[(b, k)]])
if cyc and n % 2 == 0:
    # Z_m invariance: orientation and extra colour shifted-invariant (extra colours fixed)
    def sh(x, g): return x if x == 'I' else (x + g) % m
    def she(e, g): return tuple(sorted((sh(e[0], g), sh(e[1], g)), key=str))
    for (e, f), v in ori.items():
        e2, f2 = she(e, 1), she(f, 1)
        w = ori[(e2, f2)] if (e2, f2) in ori else -ori[(f2, e2)]
        cls += [[-v, w], [v, -w]]
    for ch in cher:
        ch2 = (sh(ch[0], 1), she(ch[1], 1))
        for k in range(X): cls += [[-y[(ch, k)], y[(ch2, k)]]]
D = pathlib.Path(__file__).resolve().parents[2] / 'outputs' / 'cnf'; D.mkdir(parents=True, exist_ok=True); cnf = D / f'red{n}{"c" if cyc else ""}.cnf'
with open(cnf, 'w') as fh:
    fh.write(f'p cnf {nv} {len(cls)}\n')
    for c in cls: fh.write(' '.join(map(str, c)) + ' 0\n')
cad = '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
res = subprocess.run([cad, '-q', '-t', '110', str(cnf)], capture_output=True, text=True)
st = [l for l in res.stdout.splitlines() if l.startswith('s ')]
out = {'n': n, 'cyc': cyc, 'vars': nv, 'clauses': len(cls), 'status': st}
if st and st[0] == 's SATISFIABLE':
    lits = set(int(t) for l in res.stdout.splitlines() if l.startswith('v ') for t in l[2:].split())
    colour = {}
    for p in pairs: colour[('v', p)] = ('F', phi(*p))
    for ch in cher:
        ks = [k for k in range(X) if y[(ch, k)] in lits]
        colour[('c',) + ch] = ('X', ks[0]) if rec[ch] in lits else ('F', phi(*ch[1]))
    # independent check of total colouring of L(K_n)
    bad = 0
    for ch in cher:
        p, (s, t) = ch
        if colour[('c',) + ch] in (colour[('v', edge_of(p, s))], colour[('v', edge_of(p, t))]): bad += 1
    for p in pairs:
        a, b = p
        for q in pairs:
            if q > p and set(p) & set(q) and colour[('v', p)] == colour[('v', q)]: bad += 1
        cs = [colour[('c',) + ch] for ch in inc[p]]
        if len(set(cs)) != len(cs): bad += 1
    pal = set(colour.values())
    out.update(palette=len(pal), violations=bad)
print(json.dumps(out))
