"""341837 diagnostics: exact burnt-pancake distances by BFS for n <= NMAX.
Checks (1) source Table tab:bn values, (2) printed Conjecture con:sum,
(3) the corrected Newton form with binom(i+j,i), (4) invariance of distance under
strip reduction (collapsing adjacencies, frame element n+1 appended).
usage: burnt_bfs.py NMAX OUTJSON"""
import sys, json
from math import comb
NMAX = int(sys.argv[1]); OUT = sys.argv[2]

def flip(p, i):
    return tuple(-x for x in reversed(p[:i])) + p[i:]

def bfs(n):
    start = tuple(range(1, n + 1)); d = {start: 0}; frontier = [start]; k = 0
    while frontier:
        k += 1; nxt = []
        for p in frontier:
            for i in range(1, n + 1):
                q = flip(p, i)
                if q not in d:
                    d[q] = k; nxt.append(q)
        frontier = nxt
    return d

def reduce_(p):
    n = len(p); ext = list(p) + [n + 1]
    strips = [[ext[0]]]
    for a, b in zip(ext, ext[1:]):
        if b - a == 1: strips[-1].append(b)
        else: strips.append([b])
    strips = strips[:-1]  # last strip contains n+1: absorbed into the frame
    keys = sorted(min(abs(x) for x in s) for s in strips)
    rank = {v: r + 1 for r, v in enumerate(keys)}
    return tuple(rank[min(abs(x) for x in s)] * (1 if s[0] > 0 else -1) for s in strips)

D = {}; R = {}
for n in range(1, NMAX + 1):
    D[n] = bfs(n)
    cnt = {}
    for v in D[n].values(): cnt[v] = cnt.get(v, 0) + 1
    R[n] = cnt
    print('n', n, 'states', len(D[n]), 'diam', max(cnt), [cnt.get(k, 0) for k in range(max(cnt) + 1)], flush=True)

def Rk(k, n): return R[n].get(k, 0) if n >= 1 else (1 if k == 0 else 0)

printed_fail = []; corrected_fail = []
for k in range(1, 2 * NMAX + 2):
    for n in range(1, NMAX + 1):
        pr = sum(sum((-1) ** i * comb(i + j - 1, i) * comb(n, i + j) for i in range(k - j + 1)) * Rk(k, j) for j in range(1, k + 1) if j <= NMAX)
        co = sum(sum((-1) ** i * comb(i + j, i) * comb(n, i + j) for i in range(k - j + 1)) * Rk(k, j) for j in range(1, k + 1) if j <= NMAX)
        ok_range = k <= NMAX  # all R_k(j), j<=k, known
        if ok_range and pr != Rk(k, n): printed_fail.append((k, n, pr, Rk(k, n)))
        if ok_range and co != Rk(k, n): corrected_fail.append((k, n, co, Rk(k, n)))
print('printed formula failures (k,n,formula,true), first 10:', printed_fail[:10], 'total', len(printed_fail))
print('corrected (binom(i+j,i)) failures:', corrected_fail[:10], 'total', len(corrected_fail))

viol = []
for n in range(1, NMAX + 1):
    for p, dp in D[n].items():
        r = reduce_(p); b = len(r)
        dr = 0 if b == 0 else D[b][r]
        if dr != dp: viol.append((p, dp, r, dr))
print('reduction-invariance violations:', len(viol), viol[:10])
# adjacency-free counts I_k(b)
I = {b: {} for b in range(1, NMAX + 1)}
for b in range(1, NMAX + 1):
    for p, dp in D[b].items():
        if len(reduce_(p)) == b: I[b][dp] = I[b].get(dp, 0) + 1
json.dump(dict(R={n: R[n] for n in R}, I=I, printed_fail=printed_fail, corrected_fail=corrected_fail,
               reduction_violations=[list(map(list, (v[0], v[2]))) + [v[1], v[3]] for v in viol][:200], n_violations=len(viol)),
          open(OUT, 'w'), indent=1)
print('I_k(b):', {b: dict(sorted(I[b].items())) for b in I})
