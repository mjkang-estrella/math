"""353177: structure of the 1-flip graph on W_{q,n}: leaves, connectivity, and a randomized Hamiltonian-path search
(Posa-style rotations + backtracking fallback). Positive results are certified by the explicit path (checked)."""
import sys, random, itertools
sys.setrecursionlimit(100000)
from qdec import ok
def words(q, n):
    return [w for w in range(1 << n) if ok(tuple((w >> (n - 1 - i)) & 1 for i in range(n)), q)]
def graph(q, n):
    W = words(q, n); S = {w: i for i, w in enumerate(W)}
    adj = [[S[w ^ (1 << j)] for j in range(n) if (w ^ (1 << j)) in S] for w in W]
    return W, adj
def ham_path(adj, tries=200, seed=1):
    N = len(adj); rnd = random.Random(seed)
    if N <= 1: return list(range(N))
    for t in range(tries):
        start = rnd.randrange(N); path = [start]; pos = {start: 0}
        steps = 0
        while len(path) < N and steps < 50 * N:
            steps += 1; end = path[-1]
            nb = [v for v in adj[end] if v not in pos]
            if nb:
                v = min(nb, key=lambda v: (sum(1 for u in adj[v] if u not in pos), rnd.random()))
                pos[v] = len(path); path.append(v); continue
            # Posa rotation: pick neighbour u of end in path, reverse tail after u
            cand = [pos[u] for u in adj[end] if pos[u] < len(path) - 2]
            if not cand: break
            i = rnd.choice(cand); tail = path[i + 1:][::-1]; path = path[:i + 1] + tail
            for k in range(i + 1, len(path)): pos[path[k]] = k
        if len(path) == N: return path
    return None
def check(adj, p):
    return len(p) == len(adj) and len(set(p)) == len(p) and all(p[i + 1] in adj[p[i]] for i in range(len(p) - 1))
if __name__ == '__main__':
    qs = [int(x) for x in sys.argv[1].split(',')]; nmax = int(sys.argv[2])
    for q in qs:
        for n in range(0, nmax + 1):
            W, adj = graph(q, n); leaves = sum(1 for a in adj if len(a) == 1); iso = sum(1 for a in adj if len(a) == 0)
            p = ham_path(adj)
            print(f'q={q} n={n} |W|={len(W)} leaves={leaves} isolated={iso} hampath={"FOUND" if p and check(adj,p) else "NOT FOUND"}', flush=True)
