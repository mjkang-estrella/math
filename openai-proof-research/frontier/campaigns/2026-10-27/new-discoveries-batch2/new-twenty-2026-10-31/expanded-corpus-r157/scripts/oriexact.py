# Exact decision for one graph G = K_n - H: does some orientation make every Hamilton cycle have
# sigma_max <= T-1?  Method: Held-Karp style DP computing, for a fixed orientation, the max number of
# forward arcs over directed traversals of Hamilton cycles; combined with local search (evidence only) and
# an exact branch-and-bound over orientations of edges at vertex sets (not used here).
import sys, json, random, time, itertools
def maxfwd(n, adjo, adj):
    # adjo[u] bitmask of v with arc u->v ; adj[u] bitmask of neighbours. start at 0.
    NEG = -1
    full = (1 << n) - 1
    dp = [[NEG]*n for _ in range(1 << n)]
    dp[1][0] = 0
    for mask in range(1, 1 << n):
        if not mask & 1: continue
        row = dp[mask]
        for v in range(n):
            val = row[v]
            if val < 0: continue
            cand = adj[v] & ~mask
            while cand:
                w = (cand & -cand).bit_length() - 1; cand &= cand - 1
                nv = val + (1 if adjo[v] >> w & 1 else 0)
                r2 = dp[mask | 1 << w]
                if nv > r2[w]: r2[w] = nv
    best = -1
    for v in range(1, n):
        if dp[full][v] >= 0 and adj[v] & 1:
            best = max(best, dp[full][v] + (1 if adjo[v] & 1 else 0))
    return best
def evaluate(n, edges, orient):
    adjo = [0]*n; adj = [0]*n
    for (a, b), x in zip(edges, orient):
        adj[a] |= 1 << b; adj[b] |= 1 << a
        if x: adjo[a] |= 1 << b
        else: adjo[b] |= 1 << a
    f = maxfwd(n, adjo, adj)
    adjr = [0]*n
    for u in range(n):
        for v in range(n):
            if adjo[u] >> v & 1: adjr[v] |= 1 << u
    b = maxfwd(n, adjr, adj)
    return max(f, b)
if __name__ == '__main__':
    n = int(sys.argv[1]); H = json.loads(sys.argv[2]); T = int(sys.argv[3]); secs = float(sys.argv[4]); seed = int(sys.argv[5])
    Hs = set(map(tuple, H)); edges = [p for p in itertools.combinations(range(n), 2) if p not in Hs]
    rnd = random.Random(seed); t = time.time(); best = 99; evals = 0; found = None
    while time.time() - t < secs and found is None:
        o = [rnd.randrange(2) for _ in edges]; cur = evaluate(n, edges, o); evals += 1
        for it in range(300):
            i = rnd.randrange(len(edges)); o[i] ^= 1
            v = evaluate(n, edges, o); evals += 1
            if v <= cur or rnd.random() < 0.05: cur = v
            else: o[i] ^= 1
            best = min(best, cur)
            if cur < T: found = [list(e) if x else [e[1], e[0]] for e, x in zip(edges, o)]; break
            if time.time() - t > secs: break
    print(json.dumps({'n': n, 'H': H, 'T': T, 'best_max_sigma': best, 'evals': evals, 'found': found}))
