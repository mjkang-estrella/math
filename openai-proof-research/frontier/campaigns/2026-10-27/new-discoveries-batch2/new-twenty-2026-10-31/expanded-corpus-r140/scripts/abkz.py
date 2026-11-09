"""Bounded search, MathDB 369320 (Aharoni-Berger-Kotlar-Ziv 2017 conjecture, as
Conjecture 1.15 of arXiv:2507.12100v2), restricted to M1, M2 partition matroids,
i.e. E = edge multiset of a bipartite multigraph, common independent sets =
matchings, 'E partitions into k independent sets in both' <=> max degree <= k
(Koenig).  For a partition of E into parts S_i we need a matching X with
|X & S_i| >= floor(|S_i|/k) - 1 for all i.  Random instances + hill climbing on
the deficiency; exhaustive matching check.  Seeded, bounded; diagnostics only.
Usage: abkz.py k seed iterations
"""
import sys, random, json

def best_slack(edges, parts, k):
    # maximize min_i (|X & S_i| - (floor(|S_i|/k)-1)) over matchings X (DFS over edges)
    need = [len(p) // k - 1 for p in parts]
    pid = {}
    for i, p in enumerate(parts):
        for e in p: pid[e] = i
    order = sorted(range(len(edges)), key=lambda e: pid[e])
    best = [-10 ** 9]
    cnt = [0] * len(parts)
    def dfs(t, usedA, usedB):
        if t == len(order):
            s = min(cnt[i] - need[i] for i in range(len(parts)))
            if s > best[0]: best[0] = s
            return best[0] >= 0
        e = order[t]; a, b = edges[e]
        if not (usedA >> a & 1) and not (usedB >> b & 1):
            cnt[pid[e]] += 1
            if dfs(t + 1, usedA | 1 << a, usedB | 1 << b): return True
            cnt[pid[e]] -= 1
        return dfs(t + 1, usedA, usedB)
    dfs(0, 0, 0)
    return best[0]

def random_instance(rng, k, nA, nB, m):
    degA = [0] * nA; degB = [0] * nB; edges = []
    tries = 0
    while len(edges) < m and tries < 1000:
        tries += 1
        a, b = rng.randrange(nA), rng.randrange(nB)
        if degA[a] < k and degB[b] < k:
            edges.append((a, b)); degA[a] += 1; degB[b] += 1
    return edges

def random_parts(rng, m, k):
    idx = list(range(m)); rng.shuffle(idx)
    r = rng.randint(1, max(1, m // (2 * k)))
    parts = [[] for _ in range(r)]
    for i, e in enumerate(idx): parts[i % r if i < r else rng.randrange(r)].append(e)
    return [p for p in parts if p]

if __name__ == '__main__':
    k, seed, iters = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    worst = None; tested = 0; fails = []
    for it in range(iters):
        nA = rng.randint(2, 6); nB = rng.randint(2, 6)
        m = rng.randint(2 * k, min(k * min(nA, nB), 16))
        E = random_instance(rng, k, nA, nB, m)
        if len(E) < 2 * k: continue
        P = random_parts(rng, len(E), k)
        s = best_slack(E, P, k); tested += 1
        # hill climb on partition: move one edge between parts to decrease slack
        for _ in range(30):
            if s < 0: break
            P2 = [list(p) for p in P]
            i = rng.randrange(len(P2))
            if not P2[i]: continue
            e = P2[i].pop(rng.randrange(len(P2[i])))
            j = rng.randrange(len(P2) + 1)
            if j == len(P2): P2.append([e])
            else: P2[j].append(e)
            P2 = [p for p in P2 if p]
            s2 = best_slack(E, P2, k); tested += 1
            if s2 <= s: P, s = P2, s2
        if worst is None or s < worst[0]: worst = (s, E, P)
        if s < 0:
            fails.append({'edges': E, 'parts': P, 'slack': s}); break
    print(json.dumps({'k': k, 'seed': seed, 'instances_tested': tested, 'min_slack_found': worst[0] if worst else None,
                      'worst_instance': {'edges': worst[1], 'parts': worst[2]} if worst else None, 'failures': fails}))
