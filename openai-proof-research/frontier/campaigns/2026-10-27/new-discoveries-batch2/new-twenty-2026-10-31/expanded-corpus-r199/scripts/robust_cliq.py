"""373107 (Filakovsky arXiv:2602.11365 v4, Conjecture after Cor. 1.4).
Square sequence graphs (Definition 2.3): start from C4; each step glues a new C4 along an
edge u-y of the current graph (2 new vertices) or along a 2-path u-y-v (1 new vertex).
k-robust clique complex Cliq_k(G) = {W subset V : W contains no independent k-set}.
Conjecture: Cliq_k(G) ~ wedge of (2k-3)-spheres, for all k >= 2.
We compute reduced GF(2) and GF(3) Betti numbers for every generated graph (deduplicated
by a Weisfeiler-Lehman hash: coverage is up to WL-equivalence, no false positives) and
every 4 <= k <= alpha(G); any reduced homology outside degree 2k-3 refutes the conjecture.
usage: robust_cliq.py nsquares_max [maxV] [kmin (default 4; 2 for sanity vs the proved k=2,3)]
"""
import sys, json, itertools, hashlib

NMAX = int(sys.argv[1]); MAXV = int(sys.argv[2]) if len(sys.argv) > 2 else 99
KMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 4

def wl_hash(nv, adj):
    col = [len(adj[v]) for v in range(nv)]
    for _ in range(nv):
        sig = [(col[v], tuple(sorted(col[w] for w in adj[v]))) for v in range(nv)]
        keys = {s: i for i, s in enumerate(sorted(set(sig)))}
        new = [keys[s] for s in sig]
        if len(set(new)) == len(set(col)): col = new; break
        col = new
    return hashlib.sha256(json.dumps(sorted((col[v], sorted(col[w] for w in adj[v])) for v in range(nv))).encode()).hexdigest()

def extensions(nv, edges):
    adj = [set() for _ in range(nv)]
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    out = []
    for (u, y) in edges:
        for (p, q) in ((u, y), (y, u)):
            x, v = nv, nv + 1
            out.append((nv + 2, edges + [(x, p), (x, v), (v, q)]))
    for y in range(nv):
        for u, v in itertools.combinations(sorted(adj[y]), 2):
            x = nv
            out.append((nv + 1, edges + [(x, u), (x, v)]))
    return out

def indep_k_masks(nv, adj, k):
    res = []
    def rec(start, chosen, mask):
        if len(chosen) == k: res.append(mask); return
        for v in range(start, nv):
            if all(v not in adj[c] for c in chosen):
                rec(v + 1, chosen + [v], mask | (1 << v))
    rec(0, [], 0); return res

def alpha(nv, adj):
    best = 0
    for m in range(1 << nv):
        if bin(m).count('1') <= best: continue
        vs = [v for v in range(nv) if m >> v & 1]
        if all(b not in adj[a] for a, b in itertools.combinations(vs, 2)): best = len(vs)
    return best

def rank_mod(cols, p):
    """rank over GF(p) of a list of sparse columns {row: coeff}"""
    pivots = {}; r = 0
    for c in cols:
        c = {i: x % p for i, x in c.items() if x % p}
        while c:
            piv = max(c)
            if piv in pivots:
                pc = pivots[piv]; f = c[piv] * pow(pc[piv], p - 2, p) % p
                for i, x in pc.items():
                    y = (c.get(i, 0) - f * x) % p
                    if y: c[i] = y
                    else: c.pop(i, None)
            else:
                pivots[piv] = c; r += 1; break
    return r

def betti(nv, faces_by_dim, p):
    idx = {d: {f: i for i, f in enumerate(fs)} for d, fs in faces_by_dim.items()}
    ranks = {}
    for d, fs in faces_by_dim.items():
        if d == -1: ranks[d] = 0; continue
        cols = []
        for f in fs:
            col = {}; sign = 1
            for v in range(nv):
                if f >> v & 1:
                    col[idx[d - 1][f & ~(1 << v)]] = sign; sign = -sign
            cols.append(col)
        ranks[d] = rank_mod(cols, p)
    top = max(faces_by_dim)
    return {d: len(faces_by_dim[d]) - ranks[d] - ranks.get(d + 1, 0) for d in range(-1, top + 1)
            if len(faces_by_dim[d]) - ranks[d] - ranks.get(d + 1, 0)}

def complex_faces(nv, ind):
    fb = {}
    for m in range(1 << nv):
        if any(m & s == s for s in ind): continue
        fb.setdefault(bin(m).count('1') - 1, []).append(m)
    return fb

seen = set(); level = [(4, [(0, 1), (1, 2), (2, 3), (3, 0)])]
stats = []; bad = []
for n in range(1, NMAX + 1):
    if n > 1:
        nxt = []
        for nv, e in level:
            for nv2, e2 in extensions(nv, e):
                if nv2 > MAXV: continue
                adj = [set() for _ in range(nv2)]
                for a, b in e2: adj[a].add(b); adj[b].add(a)
                h = wl_hash(nv2, adj)
                if h in seen: continue
                seen.add(h); nxt.append((nv2, e2))
        level = nxt
    checked = 0
    # optional chunking: argv[4]=r, argv[5]=c -> only the final level, graphs with index % c == r
    if len(sys.argv) > 5:
        R_, C_ = int(sys.argv[4]), int(sys.argv[5])
        todo = [g for i, g in enumerate(level) if i % C_ == R_] if n == NMAX else []
    else:
        todo = level
    for nv, e in todo:
        adj = [set() for _ in range(nv)]
        for a, b in e: adj[a].add(b); adj[b].add(a)
        al = alpha(nv, adj)
        for k in range(KMIN, al + 1):
            ind = indep_k_masks(nv, adj, k)
            fb = complex_faces(nv, ind)
            for p in (2, 3):
                b = betti(nv, fb, p)
                checked += 1
                if any(d != 2 * k - 3 for d in b):
                    bad.append(dict(n=n, nv=nv, edges=e, k=k, alpha=al, p=p, reduced_betti=b))
    stats.append(dict(n=n, graphs=len(level), complexes_checked=checked))
    print(json.dumps(stats[-1]), flush=True)
    if bad: break
print(json.dumps(dict(stats=stats, counterexamples=bad[:5])))
