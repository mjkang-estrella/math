"""Kamatchi-Arumugam tree conjecture (MathDB 350880): a tree T is distance antimagic (bijection f: V -> {1..n}
with pairwise distinct open-neighbourhood sums w(v) = sum_{u in N(v)} f(u)) iff no vertex is adjacent to two
or more leaves.  Necessity is immediate (two leaves on one support vertex have equal weight).
This script enumerates ALL free trees of order NMIN..NMAX (leaf-addition + AHU centre canonical form, checked
against OEIS A000055 counts), keeps those with no support vertex adjacent to >= 2 leaves, and finds a
distance-antimagic labelling for each by seeded local search, with exact backtracking as fallback.
Every found labelling is re-verified.  Usage: da_trees.py NMIN NMAX SEED OUT_JSON"""
import sys, json, random
NMIN, NMAX, SEED, OUT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
A000055 = {1: 1, 2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47, 10: 106, 11: 235, 12: 551, 13: 1301,
           14: 3159, 15: 7741, 16: 19320, 17: 48629, 18: 123867, 19: 317955}
rng = random.Random(SEED)

def centres(adj):
    n = len(adj); deg = [len(a) for a in adj]; layer = [v for v in range(n) if deg[v] <= 1]; rem = n
    removed = [False] * n
    while rem > 2:
        rem -= len(layer); nxt = []
        for v in layer:
            removed[v] = True
            for u in adj[v]:
                if not removed[u]:
                    deg[u] -= 1
                    if deg[u] == 1: nxt.append(u)
        layer = nxt
    return [v for v in range(n) if not removed[v]]

def enc(adj, v, p):
    return '(' + ''.join(sorted(enc(adj, u, v) for u in adj[v] if u != p)) + ')'

def canon(adj):
    cs = centres(adj)
    if len(cs) == 1: return enc(adj, cs[0], -1)
    a, b = cs
    x, y = enc(adj, a, b), enc(adj, b, a)
    return '2' + min(x + y, y + x)

def decode2(s):
    """Rebuild adjacency from a canonical string (one centre, or '2' + two centre-rooted halves)."""
    adj = []
    def build(i, parent):
        v = len(adj); adj.append([])
        if parent >= 0: adj[v].append(parent); adj[parent].append(v)
        i += 1
        while s[i] == '(':
            i = build(i, v)
        return i + 1
    if s[0] == '2':
        i = build(1, -1); r2 = len(adj); build(i, -1)
        adj[0].append(r2); adj[r2].append(0)
    else:
        build(0, -1)
    return adj

levels = {1: {canon([[]])}}
for n in range(2, NMAX + 1):
    cur = set()
    for s in levels[n - 1]:
        adj = decode2(s)
        for v in range(n - 1):
            a2 = [list(x) for x in adj] + [[v]]; a2[v].append(n - 1)
            cur.add(canon(a2))
    levels[n] = cur
    assert len(cur) == A000055[n], (n, len(cur))

def weights(adj, f):
    return [sum(f[u] for u in adj[v]) for v in range(len(adj))]

def collisions(w):
    seen = {}; c = 0
    for x in w:
        c += seen.get(x, 0); seen[x] = seen.get(x, 0) + 1
    return c

def local_search(adj, tries=60, steps=4000):
    n = len(adj)
    for _ in range(tries):
        f = list(range(1, n + 1)); rng.shuffle(f)
        c = collisions(weights(adj, f))
        for _ in range(steps):
            if c == 0: return f
            i, j = rng.randrange(n), rng.randrange(n)
            if i == j: continue
            f[i], f[j] = f[j], f[i]
            c2 = collisions(weights(adj, f))
            if c2 <= c: c = c2
            else: f[i], f[j] = f[j], f[i]
        if c == 0: return f
    return None

def backtrack(adj):
    n = len(adj); order = sorted(range(n), key=lambda v: -len(adj[v])); f = [0] * n; used = [False] * (n + 1)
    def ok_partial():
        # weights of vertices whose neighbourhood is fully labelled must be distinct
        ws = [sum(f[u] for u in adj[v]) for v in range(n) if all(f[u] for u in adj[v])]
        return len(ws) == len(set(ws))
    def rec(k):
        if k == n: return True
        v = order[k]
        for lab in range(1, n + 1):
            if used[lab]: continue
            f[v] = lab; used[lab] = True
            if ok_partial() and rec(k + 1): return True
            f[v] = 0; used[lab] = False
        return False
    return list(f) if rec(0) else None

summary = {}; failures = []
for n in range(NMIN, NMAX + 1):
    elig = 0; viaBT = 0
    for s in sorted(levels[n]):
        adj = decode2(s)
        assert canon(adj) == s
        leaves = [v for v in range(n) if len(adj[v]) == 1]
        if n >= 3 and any(sum(1 for u in adj[v] if len(adj[u]) == 1) >= 2 for v in range(n)):
            continue
        elig += 1
        f = local_search(adj)
        if f is None:
            f = backtrack(adj); viaBT += 1
        if f is None:
            failures.append({'n': n, 'tree': s}); continue
        w = weights(adj, f)
        assert sorted(f) == list(range(1, n + 1)) and len(set(w)) == n
    summary[n] = {'free_trees': len(levels[n]), 'eligible': elig, 'needed_backtracking': viaBT}
    print(n, summary[n], 'failures so far', len(failures), flush=True)
json.dump({'summary': summary, 'failures': failures, 'seed': SEED}, open(OUT, 'w'), indent=1)
