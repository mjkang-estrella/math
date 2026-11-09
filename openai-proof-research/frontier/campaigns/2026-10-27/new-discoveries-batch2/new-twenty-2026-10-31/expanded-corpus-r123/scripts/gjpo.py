# 346238: GPO / GJPO (Chang-Ezerman-Fahreza-Wang, arXiv:2004.09810v2, Algorithms 1 and 3)
# States are n-bit ints, c0 = most significant bit.  Standard f does not depend on x0.
# Interpretation (validated on Example 7 of the source): at state c,
#   nf = (c1..c_{n-1}, f(c)), no = (c1..c_{n-1}, 1-f(c));
#   if nf in E (labels of the rooted spanning tree, unused): c <- nf, remove nf from E;
#   else: c <- no if no has not appeared, else nf.
# A rooted spanning tree of the PAG: each non-root component G_i picks one PCP edge
# G_i -> G_j labelled by w in C_i whose companion (last bit flipped) is a leaf in G_j,
# and following the edges from every component reaches the root.
import itertools, sys, json, time
from collections import Counter

def analyse(n, f):
    N = 1 << n; mask = N - 1
    succ = [((v << 1) & mask) | f(v) for v in range(N)]
    comp = [-1] * N; cycles = []
    for v in range(N):
        if comp[v] >= 0: continue
        path = []; pos = {}; u = v
        while comp[u] < 0 and u not in pos:
            pos[u] = len(path); path.append(u); u = succ[u]
        if comp[u] >= 0: idx = comp[u]
        else: idx = len(cycles); cycles.append(path[pos[u]:])
        for z in path: comp[z] = idx
    return succ, comp, cycles

def run(n, succ, E, u):
    mask = (1 << n) - 1; E = set(E); seen = {u}; c = u; bits = [u >> (n - 1)]
    for _ in range(1 << n):
        nf = succ[c]; no = nf ^ 1
        if nf in E: c = nf; E.discard(nf)
        elif no not in seen: c = no
        else: c = nf
        if c == u: break
        if c in seen: return None
        seen.add(c); bits.append(c >> (n - 1))
    if c != u or len(seen) != (1 << n): return None
    return bits

def canon_cyc(bits):
    s = ''.join(map(str, bits)); L = len(s); d = s + s
    return min(d[i:i + L] for i in range(L))

def trees(cycles, comp, cap):
    t = len(cycles)
    out_edges = [[(comp[w ^ 1], w) for w in cycles[i] if comp[w ^ 1] != i] for i in range(t)]
    res = []
    for root in range(t):
        others = [j for j in range(t) if j != root]
        for choice in itertools.product(*[out_edges[j] for j in others]):
            par = {j: e[0] for j, e in zip(others, choice)}
            ok = True
            for j in others:
                seen = set(); u = j
                while u != root and u not in seen: seen.add(u); u = par[u]
                if u != root: ok = False; break
            if ok:
                res.append((root, frozenset(e[1] for e in choice)))
                if len(res) > cap: return res, True
    return res, False

def check(n, f, cap=10**6):
    succ, comp, cycles = analyse(n, f)
    T, trunc = trees(cycles, comp, cap)
    seqs = Counter(); bad = 0; pairs = 0
    for root, E in T:
        for u in cycles[root]:
            b = run(n, succ, E, u)
            if b is None: bad += 1; continue
            seqs[canon_cyc(b)] += 1; pairs += 1
    return {'components': len(cycles), 'rooted_trees': len(T), 'truncated': trunc, 'pairs': pairs,
            'non_debruijn_runs': bad, 'inequivalent': len(seqs),
            'multiplicity_histogram': dict(Counter(seqs.values()))}

def Fh(n, m, g_truth):
    # F_h(x) = x_{n-m} + g(x_{n-m+1},...,x_{n-1}); g given by truth table on m-1 bits
    lowmask = (1 << (m - 1)) - 1
    def f(v):
        a = v & ((1 << m) - 1)
        return (a >> (m - 1)) ^ ((g_truth >> (a & lowmask)) & 1)
    return f

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'example7':
        # h = x0+x1+x2+x3, n=5, m=4: g = x1+x2+x3 = parity of 3 low bits
        gt = sum(1 << a for a in range(8) if bin(a).count('1') % 2)
        print('Example 7', check(5, Fh(5, 4, gt)))
        # Example 3: f = x1 + x2 x3, n = 4 (not of F_h form)
        f3 = lambda v: ((v >> 2) & 1) ^ (((v >> 1) & 1) & (v & 1))
        print('Example 3', check(4, f3))
    else:
        m = int(sys.argv[2]); n = int(sys.argv[3]); lo = int(sys.argv[4]); hi = int(sys.argv[5]); out = sys.argv[6]
        t0 = time.time(); summary = Counter(); witnesses = []
        for gt in range(lo, min(hi, 1 << (1 << (m - 1)))):
            r = check(n, Fh(n, m, gt), cap=200000)
            summary['h'] += 1; summary['pairs'] += r['pairs']; summary['trees'] += r['rooted_trees']
            summary['bad'] += r['non_debruijn_runs']; summary['trunc'] += r['truncated']
            if r['inequivalent'] != r['pairs']:
                witnesses.append({'g_truth': gt, **r}); print('COLLISION', m, n, gt, r, flush=True)
                if len(witnesses) >= 5: break
        res = {'m': m, 'n': n, 'g_range': [lo, hi], 'summary': dict(summary), 'witnesses': witnesses,
               'seconds': round(time.time() - t0, 1)}
        json.dump(res, open(out, 'w'), indent=1); print(res)
