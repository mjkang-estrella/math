# Independent brute-force checker for a digraph given as out-neighbour lists (JSON).
# Reports strongness, Hamiltonicity (by permutations), and the minimum degree sum over
# non-adjacent dominating pairs and over non-adjacent dominated pairs.
import sys, json, itertools
out = json.loads(sys.argv[1]); n = len(out)
A = {(i, j) for i in range(n) for j in out[i]}
assert all(i != j for i, j in A)
def reach(adj):
    seen = {0}; st = [0]
    while st:
        v = st.pop()
        for w in adj(v):
            if w not in seen: seen.add(w); st.append(w)
    return len(seen) == n
strong = reach(lambda v: [j for j in range(n) if (v, j) in A]) and reach(lambda v: [j for j in range(n) if (j, v) in A])
ham = any(all((c[k], c[(k + 1) % n]) in A for k in range(n)) for c in ([0] + list(p) for p in itertools.permutations(range(1, n))))
deg = [sum((i, j) in A for j in range(n)) + sum((j, i) in A for j in range(n)) for i in range(n)]
dom = []; domd = []
for x, y in itertools.combinations(range(n), 2):
    if (x, y) in A or (y, x) in A: continue
    if any((x, z) in A and (y, z) in A for z in range(n)): dom.append(deg[x] + deg[y])
    if any((z, x) in A and (z, y) in A for z in range(n)): domd.append(deg[x] + deg[y])
print(json.dumps(dict(n=n, arcs=len(A), strong=strong, hamiltonian=ham, degrees=deg, threshold=2 * n - 1,
    min_dominating_pair_sum=min(dom) if dom else None, min_dominated_pair_sum=min(domd) if domd else None)))
