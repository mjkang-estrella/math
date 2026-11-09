# Independent reviewer code for MathDB 332037 (Smyth, arXiv:1512.04084 v1, Conjecture 1.5).
# Written from the source definitions (TeX lines 24-28, 73-79); imports nothing from the discovery lane.
#   U^m_n : maps [m] -> N with sum n ; concatenation lambda mu ; lambda_p = non-increasing rearrangement ;
#   lambda dominates mu (lambda |> mu) iff |lambda| = |mu| and sum_{i<=j} lambda_p(i) >= sum_{i<=j} mu_p(i) for all j >= 1.
#   Conjecture: injection gamma : U^A_b x U^B_a -> U^A_a x U^B_b with lambda1 mu1 |> lambda2 mu2.
import sys, json, hashlib, time
from collections import Counter, deque

def comps(m, n):
    """All tuples of length m of non-negative integers with sum n (recursive, no itertools)."""
    if m == 0:
        return [()] if n == 0 else []
    out = []
    for first in range(n + 1):
        for rest in comps(m - 1, n - first):
            out.append((first,) + rest)
    return out

def rearr(t):
    return tuple(sorted(t, reverse=True))

def dom(p, q):
    """p |> q for finite sequences (rearranged, zero padded)."""
    p = rearr(p); q = rearr(q)
    L = max(len(p), len(q))
    p = p + (0,) * (L - len(p)); q = q + (0,) * (L - len(q))
    if sum(p) != sum(q):
        return False
    sp = sq = 0
    for j in range(L):
        sp += p[j]; sq += q[j]
        if sp < sq:
            return False
    return True

def partitions_le(n, k, mx=None):
    """Partitions of n into at most k parts, as non-increasing k-tuples padded with zeros."""
    if mx is None: mx = n
    if k == 0:
        return [()] if n == 0 else []
    out = []
    for f in range(min(n, mx), -1, -1):
        if f * k < n: break
        for rest in partitions_le(n - f, k - 1, f):
            out.append((f,) + rest)
    return out

def type_counts(A, a, B, b):
    """Multiplicities of rearranged concatenation types for X = U^A_b x U^B_a and Y = U^A_a x U^B_b."""
    X = Counter(); Y = Counter()
    UAb, UBa, UAa, UBb = comps(A, b), comps(B, a), comps(A, a), comps(B, b)
    for l in UAb:
        for m in UBa:
            X[rearr(l + m)] += 1
    for l in UAa:
        for m in UBb:
            Y[rearr(l + m)] += 1
    return X, Y, (len(UAb), len(UBa), len(UAa), len(UBb))

class Dinic:
    def __init__(s, n):
        s.n = n; s.g = [[] for _ in range(n)]
    def add(s, u, v, c):
        s.g[u].append([v, c, len(s.g[v])]); s.g[v].append([u, 0, len(s.g[u]) - 1])
    def bfs(s, src, snk):
        s.lv = [-1] * s.n; s.lv[src] = 0; q = deque([src])
        while q:
            u = q.popleft()
            for v, c, _ in s.g[u]:
                if c > 0 and s.lv[v] < 0:
                    s.lv[v] = s.lv[u] + 1; q.append(v)
        return s.lv[snk] >= 0
    def dfs(s, u, snk, f):
        if u == snk: return f
        while s.it[u] < len(s.g[u]):
            e = s.g[u][s.it[u]]; v, c, r = e
            if c > 0 and s.lv[v] == s.lv[u] + 1:
                d = s.dfs(v, snk, min(f, c))
                if d > 0:
                    e[1] -= d; s.g[v][r][1] += d; return d
            s.it[u] += 1
        return 0
    def maxflow(s, src, snk):
        F = 0
        while s.bfs(src, snk):
            s.it = [0] * s.n
            while True:
                f = s.dfs(src, snk, 1 << 60)
                if not f: break
                F += f
        return F

def max_injection(A, a, B, b):
    X, Y, sizes = type_counts(A, a, B, b)
    xs = sorted(X); ys = sorted(Y)
    n = 2 + len(xs) + len(ys); src, snk = 0, 1
    D = Dinic(n); INF = 1 << 50
    for i, p in enumerate(xs):
        D.add(src, 2 + i, X[p])
        for j, q in enumerate(ys):
            if dom(p, q):
                D.add(2 + i, 2 + len(xs) + j, INF)
    for j, q in enumerate(ys):
        D.add(2 + len(xs) + j, snk, Y[q])
    sys.setrecursionlimit(10000)
    F = D.maxflow(src, snk)
    # min cut: X types reachable from the source in the residual graph form a Hall violator.
    reach = set(); dq = deque([src]); seen = {src}
    while dq:
        u = dq.popleft()
        for v, c, _ in D.g[u]:
            if c > 0 and v not in seen:
                seen.add(v); dq.append(v)
    Sx = [xs[i] for i in range(len(xs)) if 2 + i in seen]
    NS = [q for q in ys if any(dom(p, q) for p in Sx)]
    nX = sum(X.values()); nY = sum(Y.values())
    hall = sum(X[p] for p in Sx) - sum(Y[q] for q in NS)
    return {'A': A, 'a': a, 'B': B, 'b': b, '|X|': nX, '|Y|': nY, 'sizes(UAb,UBa,UAa,UBb)': sizes,
            'x_types': len(xs), 'y_types': len(ys), 'max_injection': F, 'deficiency': nX - F,
            'mincut_hall_excess': hall, 'mincut_Sx_types': len(Sx)}

def hopcroft_karp_expanded(A, a, B, b, edge_cap=8_000_000):
    """Plain Hopcroft-Karp on the element-level bipartite admissibility graph (no type reduction in the matching)."""
    UAb, UBa, UAa, UBb = comps(A, b), comps(B, a), comps(A, a), comps(B, b)
    Xs = [l + m for l in UAb for m in UBa]; Ys = [l + m for l in UAa for m in UBb]
    yt = [rearr(y) for y in Ys]; ytypes = sorted(set(yt)); ytid = {t: i for i, t in enumerate(ytypes)}
    members = [[] for _ in ytypes]
    for j, t in enumerate(yt): members[ytid[t]].append(j)
    xtypes = sorted(set(rearr(x) for x in Xs))
    admissible = {p: [k for k, q in enumerate(ytypes) if dom(p, q)] for p in xtypes}  # literal dominance test
    adj = []; E = 0
    for x in Xs:
        nb = []
        for k in admissible[rearr(x)]: nb.extend(members[k])
        adj.append(nb); E += len(nb)
        if E > edge_cap: return {'aborted_edges_over': edge_cap}
    nL, nR = len(Xs), len(Ys); INF = 1 << 30
    mL = [-1] * nL; mR = [-1] * nR
    def bfs():
        dist = [INF] * nL; q = deque()
        for u in range(nL):
            if mL[u] < 0: dist[u] = 0; q.append(u)
        found = False
        while q:
            u = q.popleft()
            for v in adj[u]:
                w = mR[v]
                if w < 0: found = True
                elif dist[w] == INF: dist[w] = dist[u] + 1; q.append(w)
        return found, dist
    def dfs(u, dist, it):
        # iterative augmenting DFS along layered graph
        stack = [u]; path = []
        while stack:
            x = stack[-1]
            advanced = False
            while it[x] < len(adj[x]):
                v = adj[x][it[x]]; it[x] += 1; w = mR[v]
                if w < 0:
                    path.append((x, v))
                    for (xx, vv) in path: mL[xx] = vv; mR[vv] = xx
                    return True
                if dist[w] == dist[x] + 1:
                    path.append((x, v)); stack.append(w); advanced = True; break
            if not advanced:
                dist[x] = INF; stack.pop()
                if path: path.pop()
        return False
    M = 0; phases = 0
    while True:
        found, dist = bfs()
        if not found: break
        phases += 1; it = [0] * nL
        for u in range(nL):
            if mL[u] < 0 and dfs(u, dist, it): M += 1
    # verify matching validity literally
    for u in range(nL):
        if mL[u] >= 0: assert mR[mL[u]] == u and dom(Xs[u], Ys[mL[u]])
    return {'|X|': nL, '|Y|': nR, 'edges': E, 'hk_phases': phases, 'max_matching': M}

def certificate(A, a, B, b, G):
    n = a + b; k = A + B
    UAb, UBa, UAa, UBb = comps(A, b), comps(B, a), comps(A, a), comps(B, b)
    universe = partitions_le(n, k)
    D = set(nu for nu in universe if any(dom(g, nu) for g in G))
    # explicit down-closure check of D inside the universe of partitions of n with <= k parts
    viol = sum(1 for nu in D for mu in universe if dom(nu, mu) and mu not in D)
    X = [(l, m) for l in UAb for m in UBa]; Y = [(l, m) for l in UAa for m in UBb]
    S = sorted(x for x in X if rearr(x[0] + x[1]) in D)
    T = sorted(y for y in Y if rearr(y[0] + y[1]) in D)
    # sanity: generators are partitions of n with <= k parts and pairwise incomparable (antichain)
    gens_ok = all(sum(g) == n and len(g) <= k and tuple(g) == rearr(g) for g in G)
    anti = [(i, j) for i in range(len(G)) for j in range(len(G)) if i != j and dom(G[i], G[j])]
    # are all generators realised as types of S (i.e. is each generator necessary as a type?)
    stypes = set(rearr(x[0] + x[1]) for x in S)
    return {'|UAb|': len(UAb), '|UBa|': len(UBa), '|UAa|': len(UAa), '|UBb|': len(UBb), '|X|': len(X), '|Y|': len(Y),
            'universe_partitions': len(universe), '|D|': len(D), 'downclosure_violations': viol,
            '|S|': len(S), '|T|': len(T), 'gens_ok': gens_ok, 'gen_comparable_pairs': anti,
            'gens_realised_in_X': [tuple(g) in stypes for g in G],
            'S_sha256_json': hashlib.sha256(json.dumps([[list(l), list(m)] for l, m in S]).encode()).hexdigest(),
            'T_sha256_json': hashlib.sha256(json.dumps([[list(l), list(m)] for l, m in T]).encode()).hexdigest()}

if __name__ == '__main__':
    mode = sys.argv[1]; t0 = time.time()
    G = [(13,12,8,4,2),(13,13,7,3,3),(12,12,8,6,1),(14,12,6,4,3),(13,11,7,7,1),(14,11,6,6,2),(15,11,5,5,3),(16,10,5,4,4)]
    if mode == 'cert':
        print(json.dumps(certificate(3, 20, 2, 19, G)))
    elif mode == 'flow':
        for s in sys.argv[2:]:
            A, a, B, b = map(int, s.split(','))
            print(json.dumps(max_injection(A, a, B, b)), flush=True)
    elif mode == 'hk':
        A, a, B, b = map(int, sys.argv[2].split(','))
        print(json.dumps(hopcroft_karp_expanded(A, a, B, b)))
    elif mode == 'sweep':
        # all A>=B>=0 (A<=Amax), a>b>=0 (a<=amax), a+b<=nmax, B>=2, A>B (other cases trivially true)
        Amax, amax, nmax = map(int, sys.argv[2:5]); Amin = int(sys.argv[5]) if len(sys.argv) > 5 else 0; fails = []; cnt = 0
        for A in range(Amin, Amax + 1):
            for B in range(2, A):
                for a in range(0, amax + 1):
                    for b in range(0, a):
                        if a + b > nmax: continue
                        r = max_injection(A, a, B, b); cnt += 1
                        if r['deficiency']: fails.append(r)
        print(json.dumps({'Amin': Amin, 'Amax': Amax, 'amax': amax, 'nmax': nmax, 'nontrivial_cases': cnt, 'failures': fails}))
    elif mode == 'trivial':
        # brute-force check of the claimed explicit injections for A=B (swap), a=b (identity), B=1 (shift)
        bad = 0; cases = 0
        for A in range(0, 7):
            for a in range(0, 9):
                for b in range(0, a + 1):
                    for B in range(0, A + 1):
                        if not (A == B or a == b or B == 1): continue
                        cases += 1
                        img = set()
                        for l in comps(A, b):
                            for m in comps(B, a):
                                if A == B: l2, m2 = m, l
                                elif a == b: l2, m2 = l, m
                                else: l2, m2 = (l[0] + a - b,) + l[1:], (b,)
                                assert sum(l2) == a and sum(m2) == b and len(l2) == A and len(m2) == B
                                if not dom(l + m, l2 + m2): bad += 1
                                img.add((l2, m2))
                        if len(img) != len(comps(A, b)) * len(comps(B, a)): bad += 1
        print(json.dumps({'trivial_cases_checked': cases, 'violations': bad}))
    print('# elapsed', round(time.time() - t0, 2))
