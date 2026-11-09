# Search for counterexamples to the Correa-Goemans proportional-factor question (MathDB 388092).
# Exact rational arithmetic for floor/ceil; DFS over edge colours with per-vertex interval pruning.
import sys, random, json, itertools
from fractions import Fraction as F
from math import floor, ceil

def bounds(c, d):
    return [(floor(ci * d), ceil(ci * d)) for ci in c]

def solvable(nv, edges, c):
    k = len(c); deg = [0] * nv
    for u, v in edges: deg[u] += 1; deg[v] += 1
    B = [bounds(c, deg[v]) for v in range(nv)]
    cnt = [[0] * k for _ in range(nv)]; rem = deg[:]
    order = sorted(range(len(edges)), key=lambda e: -(deg[edges[e][0]] + deg[edges[e][1]]))
    def ok(v):
        need = sum(max(0, B[v][i][0] - cnt[v][i]) for i in range(k))
        room = sum(B[v][i][1] - cnt[v][i] for i in range(k))
        return need <= rem[v] <= room
    def dfs(j):
        if j == len(order): return True
        u, v = edges[order[j]]
        rem[u] -= 1; rem[v] -= 1
        for i in range(k):
            if cnt[u][i] < B[u][i][1] and cnt[v][i] < B[v][i][1]:
                cnt[u][i] += 1; cnt[v][i] += 1
                if ok(u) and ok(v) and dfs(j + 1): return True
                cnt[u][i] -= 1; cnt[v][i] -= 1
        rem[u] += 1; rem[v] += 1
        return False
    if not all(ok(v) for v in range(nv)): return False
    return dfs(0)

def randgraph(a, b, p, rng, multi=False):
    E = []
    for i in range(a):
        for j in range(b):
            m = rng.randint(0, 2) if multi else (1 if rng.random() < p else 0)
            E += [(i, a + j)] * m
    return a + b, E

if __name__ == '__main__':
    seed = int(sys.argv[1]); trials = int(sys.argv[2]); k = int(sys.argv[3]); multi = sys.argv[4] == 'multi'
    rng = random.Random(seed)
    for t in range(trials):
        a, b = rng.randint(2, 5), rng.randint(2, 5)
        nv, E = randgraph(a, b, rng.uniform(0.4, 0.9), rng, multi)
        if not E: continue
        N = rng.randint(k, 13)
        while True:
            cuts = sorted(rng.sample(range(1, N), k - 1)) if N - 1 >= k - 1 else None
            if cuts: break
            N += 1
        parts = [x - y for x, y in zip(cuts + [N], [0] + cuts)]
        c = [F(p, N) for p in parts]
        if not solvable(nv, E, c):
            print(json.dumps({'COUNTEREXAMPLE': True, 'nv': nv, 'a': a, 'edges': E, 'c': [str(x) for x in c]})); sys.stdout.flush()
    print(json.dumps({'done': trials, 'seed': seed, 'k': k, 'multi': multi}))
