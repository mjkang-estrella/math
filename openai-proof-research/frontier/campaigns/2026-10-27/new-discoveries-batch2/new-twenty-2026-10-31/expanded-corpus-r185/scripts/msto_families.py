import sys, pathlib, itertools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from msto import *

def kab(a, b):
    n = a + b; return n, from_edges(n, [(i, a + j) for i in range(a) for j in range(b)])

def report(name, n, adj):
    mu, ds = deltas(n, adj)
    if not ds: print(name, 'complete'); return
    best = max(ds, key=lambda x: x[1])
    neg = sum(1 for _, d in ds if d < 0)
    print(f'{name:28s} n={n} mu={float(mu):.5f} nonedges={len(ds)} decreasing={neg} max_delta={float(best[1]):+.6f} at {best[0]}', flush=True)
    return best[1]

which = sys.argv[1]
if which == 'sanity':
    for m in range(4, 10):
        n, adj = kab(2, m); report(f'K2,{m}', n, adj)
if which == 'kab':
    for a in range(2, 5):
        for b in range(a, 12 - a):
            n, adj = kab(a, b); report(f'K{a},{b}', n, adj)
if which == 'barbell':
    # two cliques K_w joined by path with p internal vertices
    for w in range(3, 6):
        for p in range(0, 12 - 2 * w + 1):
            n = 2 * w + p
            E = [(i, j) for i in range(w) for j in range(i + 1, w)]
            E += [(w + p + i, w + p + j) for i in range(w) for j in range(i + 1, w)]
            chain = [w - 1] + list(range(w, w + p)) + [w + p]
            E += list(zip(chain, chain[1:]))
            report(f'barbell w={w} p={p}', n, from_edges(n, E))
if which == 'lollipop':
    for w in range(3, 8):
        for p in range(1, 12 - w + 1):
            n = w + p
            E = [(i, j) for i in range(w) for j in range(i + 1, w)]
            chain = [w - 1] + list(range(w, w + p))
            E += list(zip(chain, chain[1:]))
            report(f'lollipop w={w} p={p}', n, from_edges(n, E))
if which == 'kabpair':
    a, b = int(sys.argv[2]), int(sys.argv[3])
    n, adj = kab(a, b)
    T = tau_table(n, adj); N, R = NR(T)
    mu = Fraction(R, N)
    for (u, v) in [(0, 1), (a, a + 1)]:
        if u == v or (u >= n or v >= n): continue
        A, B = pair_sums(n, T, u, v)
        d = Fraction(R + B, N + A) - mu
        print(f'K{a},{b} n={n} N={N} R={R} mu={float(mu):.6f} edge {u},{v}: A={A} B={B} delta={float(d):+.8f} exact_sign={(d>0)-(d<0)}', flush=True)
