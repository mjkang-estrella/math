"""Exact solver: near 1-factor of K_v (vertices Z_v, isolated vertex 0 WLOG by rotation) with prescribed length multiset.
Exhaustive DFS with memo on (unmatched mask, remaining counts), MRV branching on a vertex with fewest options,
and divisor-parity pruning: for each divisor d>1 of v, the residue classes mod d with an odd number of unmatched vertices
can only be repaired by edges whose length is not a multiple of d (each repairs at most 2 classes).
Returns a solution (list of edges) or None (proved impossible by exhaustion).
"""
import sys

def make_solver(v):
    n = (v - 1) // 2
    divs = [d for d in range(3, v) if v % d == 0]
    classmask = {d: [sum(1 << x for x in range(v) if x % d == r) for r in range(d)] for d in divs}

    def solve(counts):
        counts = list(counts)
        memo = set()
        sol = []
        nodes = [0]
        def feasible(mask):
            for d in divs:
                odd = sum(1 for cm in classmask[d] if bin(mask & cm).count('1') & 1)
                if odd:
                    rem = sum(counts[l] for l in range(1, n + 1) if l % d)
                    if odd > 2 * rem: return False
            return True
        def dfs(mask):
            if mask == 0: return True
            key = (mask, tuple(counts))
            if key in memo: return False
            nodes[0] += 1
            if not feasible(mask):
                memo.add(key); return False
            # MRV: vertex with fewest options
            best = None; bestopts = None
            m = mask
            while m:
                b = m & -m; m ^= b; x = b.bit_length() - 1
                opts = []
                for l in range(1, n + 1):
                    if counts[l]:
                        for y in {(x + l) % v, (x - l) % v}:
                            if (mask >> y) & 1 and y != x: opts.append((l, y))
                if best is None or len(opts) < len(bestopts):
                    best, bestopts = x, opts
                    if len(opts) <= 1: break
            x = best
            for l, y in bestopts:
                counts[l] -= 1
                sol.append((x, y, l))
                if dfs(mask & ~(1 << x) & ~(1 << y)):
                    counts[l] += 1; return True
                sol.pop(); counts[l] += 1
            memo.add(key)
            return False
        full = ((1 << v) - 1) & ~1
        ok = dfs(full)
        return (list(sol) if ok else None), nodes[0]
    return solve

def counts_of(v, L):
    n = (v - 1) // 2; c = [0] * (n + 1)
    for x in L: c[x] += 1
    return c

if __name__ == '__main__':
    v = int(sys.argv[1]); L = [int(x) for x in sys.argv[2].split(',')]
    solve = make_solver(v)
    sol, nodes = solve(counts_of(v, L))
    print('v', v, 'L', L, 'nodes', nodes, 'solution' if sol else 'IMPOSSIBLE', sol)
    if sol:
        used = sorted(l for _, _, l in sol); assert used == sorted(L)
        vs = sorted([a for a, b, l in sol] + [b for a, b, l in sol]); assert vs == list(range(1, v))
        assert all(min((a - b) % v, (b - a) % v) == l for a, b, l in sol)
        print('verified')
