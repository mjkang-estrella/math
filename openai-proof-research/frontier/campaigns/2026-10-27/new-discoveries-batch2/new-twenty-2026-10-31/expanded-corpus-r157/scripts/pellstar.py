# 367590: for Pell solutions (2n+1)^2-2(2m+1)^2=-1, partition {1..m} into blocks with sums exactly m+1..n.
# Stars: leaves = block elements (edge labels), centres = block sums -> (1,1)-antimagic disjoint union of stars.
# DFS: assign to each element (largest first) a target; blocks of size 2 or 3.  Verification of the labeling.
import json, sys
sys.setrecursionlimit(100000)
sols = []; n, m = 3, 2
while n < int(sys.argv[2]):
    assert (2*n+1)**2 - 2*(2*m+1)**2 == -1
    sols.append((n, m)); n, m = 3*n + 4*m + 3, 2*n + 3*m + 2
def solve(n, m):
    # elements m, m-1, ..., 1 placed into bins with capacities m+1..n; exact fill required.
    res = {s: s for s in range(m+1, n+1)}; content = {s: [] for s in res}
    nodes = [0]
    def dfs(x):
        nodes[0] += 1
        if nodes[0] > 3*10**6: return False
        if x == 0: return all(v == 0 for v in res.values())
        # prune: total residual equals sum 1..x automatically; residual r with 0<r must be >=1 fine
        opts = [s for s in res if res[s] == x] + sorted([s for s in res if res[s] > x and res[s] - x >= 1], key=lambda s: -res[s])
        tried = set()
        for s in opts:
            r = res[s]
            if r in tried: continue
            tried.add(r)
            # a bin whose residual after placement is < x but > 0 must be fillable by smaller distinct elements later: ok
            res[s] -= x; content[s].append(x)
            if dfs(x-1): return True
            res[s] += x; content[s].pop()
        return False
    ok = dfs(m)
    blocks = [(s, sorted(content[s])) for s in sorted(content)] if ok else []
    return ok, blocks, nodes[0]
out = []
for n, m in sols:
    ok, blocks, nodes = solve(n, m)
    rec = {'n': n, 'm': m, 'found': ok, 'dfs_nodes': nodes}
    if ok:
        sums = []
        for s, blk in blocks:
            assert len(blk) >= 2 and sum(blk) == s and len(set(blk)) == len(blk)
            sums += blk + [s]
        assert sorted(sums) == list(range(1, n+1))
        h = {}
        for s, b in blocks: h[len(b)] = h.get(len(b), 0) + 1
        rec.update({'stars': len(blocks), 'sizes': h, 'blocks': blocks if n < 200 else blocks[:5]})
    out.append(rec)
json.dump(out, open(sys.argv[1], 'w'), indent=1)
for r in out: print({k: v for k, v in r.items() if k != 'blocks'})
