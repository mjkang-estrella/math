"""Optimized, resumable flip-graph exploration for MathDB 368931 (Conjecture 3.8 of
arXiv:2506.16598v2).  Model identical to multitri.py (see its docstring).
State file work/mt2-k{k}-n{n}.json holds seen triangulations, BFS queue index and
results; each call runs for at most BUDGET seconds of CPU then saves.
Usage: mt2.py k n budget_seconds
"""
import sys, json, time, pathlib
from math import comb
D = pathlib.Path(__file__).resolve().parents[1]

def setup(n, k):
    C = [(r, l) for l in range(k + 1, k * n + 1) for r in range(n)]
    idx = {c: i for i, c in enumerate(C)}
    Lmax = k * n
    # for each class c, translates (d, t) of classes crossing e0=(r, r+l)
    X = []
    for (r, l) in C:
        a0, b0 = r, r + l
        lst = []
        for (s, m) in C:
            for t in range(-(Lmax // n) - 3, (Lmax // n) + 4):
                a, b = s + t * n, s + t * n + m
                if (a < a0 < b < b0) or (a0 < a < b0 < b):
                    lst.append((idx[(s, m)], a, b))
        lst.sort(key=lambda x: (x[1], x[2]))
        # pairwise crossing bitmasks among lst (forward only)
        fw = []
        for i, (_, a, b) in enumerate(lst):
            mask = 0
            for j in range(i + 1, len(lst)):
                _, a2, b2 = lst[j]
                if a < a2 < b < b2:
                    mask |= 1 << j
            fw.append(mask)
        X.append((lst, fw))
    return C, idx, X

def crossing_with(Smask, ci, X, k):
    lst, fw = X[ci]
    S = Smask | (1 << ci)
    avail = 0
    for j, (d, a, b) in enumerate(lst):
        if (S >> d) & 1:
            avail |= 1 << j
    # find k-clique in forward graph restricted to avail
    def dfs(cand, depth):
        if depth == k:
            return True
        while cand:
            low = cand & -cand
            j = low.bit_length() - 1
            cand ^= low
            if dfs(cand & fw[j], depth + 1):
                return True
        return False
    return dfs(avail, 0)

def maximal_supersets(Smask, C, X, k):
    N = len(C)
    cands = [c for c in range(N) if not (Smask >> c) & 1 and not crossing_with(Smask, c, X, k)]
    res = set()
    def rec(cur, cands):
        if not cands:
            for c in range(N):
                if not (cur >> c) & 1 and not crossing_with(cur, c, X, k):
                    return
            res.add(cur)
            return
        c = cands[0]
        cur2 = cur | (1 << c)
        rec(cur2, [d for d in cands[1:] if not crossing_with(cur2, d, X, k)])
        rec(cur, cands[1:])
    rec(Smask, cands)
    return res

def check(Tmask, C, n, k):
    full = [C[i] for i in range(len(C)) if (Tmask >> i) & 1] + [(r, k) for r in range(n)]
    W = 4 * k * n + 4
    adj = {}
    for (r, l) in full:
        a0 = -W + ((r + W) % n)
        for a in range(a0, W, n):
            adj.setdefault(a, set()).add(a + l)
            adj.setdefault(a + l, set()).add(a)
    BIG = 10 ** 6
    bad = []
    nrel = 0
    for v in range(n):
        key = lambda x, v=v: 0 if x == v else ((x - v) if x > v else (x - v + BIG))
        nb = sorted(adj[v], key=key)
        for t in range(len(nb) - 1):
            w, u = nb[t], nb[t + 1]
            if not ((k < abs(u - v) < k * n) or (k < abs(w - v) < k * n)):
                continue
            nrel += 1
            kw, ku = key(w), key(u)
            m = 2 * k + 1
            y = [None] * m
            y[0], y[k], y[k + 1] = v, w, u
            order = []
            for s in range(1, k):
                order.append(s); order.append(k + 1 + s)
            # order: 1, k+2, 2, k+3, ... ; partner of position p is p+k mod m (already assigned)
            found = []
            def ok_pos(p, x):
                kx = key(x)
                # cyclic order: positions 1..k-1 in (v,w), k+2..2k in (u, v) increasing
                prev = y[p - 1]
                if prev is None: return False
                if not (key(prev) < kx): return False
                nxt = y[(p + 1) % m]
                if nxt is not None and not (kx < (key(nxt) if nxt != v else 2 * BIG)): return False
                if 1 <= p <= k - 1 and not (kx < kw): return False
                if p >= k + 2 and not (kx > ku): return False
                return True
            def dfs(i):
                if len(found) > 1: return
                if i == len(order):
                    for j in range(m):
                        a, b = y[j], y[(j + k) % m]
                        if b not in adj.get(a, ()): return
                    found.append(list(y)); return
                p = order[i]
                partner = y[(p + k) % m]
                for x in sorted(adj.get(partner, ())):
                    if x in y: continue
                    if ok_pos(p, x):
                        y[p] = x
                        dfs(i + 1)
                        y[p] = None
            dfs(0)
            if len(found) != 1:
                bad.append({'v': v, 'w': w, 'u': u, 'stars_found': len(found), 'stars': found})
    return bad, nrel

if __name__ == '__main__':
    k, n, budget = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    C, idx, X = setup(n, k)
    st = D / f'work/mt2-k{k}-n{n}.json'
    if st.exists():
        S = json.loads(st.read_text())
        queue = S['queue']; qi = S['qi']; seen = set(queue); res = S['res']
    else:
        T0 = 0
        for c in range(len(C)):
            if not crossing_with(T0, c, X, k):
                T0 |= 1 << c
        queue = [T0]; qi = 0; seen = {T0}
        b, nr = check(T0, C, n, k)
        res = {'checked': 1, 'failing': [] if not b else [{'T': [C[i] for i in range(len(C)) if T0 >> i & 1], 'bad': b}], 'sizes': {}, 'relevant_angles': nr}
    t0 = time.process_time()
    while qi < len(queue) and time.process_time() - t0 < budget and len(res['failing']) < 3:
        T = queue[qi]; qi += 1
        for e in range(len(C)):
            if (T >> e) & 1:
                for T2 in maximal_supersets(T & ~(1 << e), C, X, k):
                    if T2 not in seen:
                        seen.add(T2); queue.append(T2)
                        b, nr = check(T2, C, n, k)
                        res['checked'] += 1; res['relevant_angles'] += nr
                        sz = str(bin(T2).count('1')); res['sizes'][sz] = res['sizes'].get(sz, 0) + 1
                        if b:
                            res['failing'].append({'T': [C[i] for i in range(len(C)) if T2 >> i & 1], 'bad': b})
    st.write_text(json.dumps({'queue': queue, 'qi': qi, 'res': res}))
    print(json.dumps({'k': k, 'n': n, 'explored': len(queue), 'expanded': qi, 'bfs_complete': qi >= len(queue),
                      'conj67_prediction': comb(2 * (n - 1), n - 1) ** k, 'checked': res['checked'],
                      'relevant_angles': res['relevant_angles'], 'sizes': res['sizes'],
                      'num_failing': len(res['failing']), 'failing': res['failing'][:1]}), flush=True)
