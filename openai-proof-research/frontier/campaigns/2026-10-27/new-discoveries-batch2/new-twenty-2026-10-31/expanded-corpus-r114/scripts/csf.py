# Chromatic symmetric functions of unicyclic graphs (Conjecture 8.1 of arXiv:2505.06486, MathDB 368352).
# X_G = sum over edge subsets S of (-1)^{|S|} p_{lambda(S)} (Stanley), lambda(S) = component sizes of (V,S).
# Graph = cycle C_c with rooted trees T_0..T_{c-1} at cycle vertices (same canonical enumeration as unicyclic.py).
# For a rooted tree: map (root component size, sorted tuple of closed component sizes) -> signed coefficient.
# For the cycle: sum over subsets of cycle edges; arcs of consecutive chosen edges merge root components.
# Groups graphs by X_G, then compares degree sequence, number of non-trivial rooted trees and internal edges.
import sys, itertools, json
from collections import defaultdict
import os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'unicyclic.py')).read()
NMAX = int(sys.argv[1]); C = int(sys.argv[2])
exec(src.split('out = {}')[0].replace('NMAX = int(sys.argv[1]); NMIN = int(sys.argv[2]) if len(sys.argv) > 2 else 3', f'NMAX={NMAX}; NMIN=3').replace('import sys, json, itertools, numpy as np', 'import sys, json, itertools'))

def merge_part(a, b):
    return tuple(sorted(a + b))

memo = {}
def tree_map(s, i):
    # rooted tree (s,i): returns dict {(rootsize, closedpartition): coeff}
    key = (s, i)
    if key in memo: return memo[key]
    cur = {(1, ()): 1}
    for (cs, ci) in trees[s][i]:
        ch = tree_map(cs, ci); nxt = defaultdict(int)
        for (r1, p1), c1 in cur.items():
            for (r2, p2), c2 in ch.items():
                nxt[(r1 + r2, merge_part(p1, p2))] -= c1 * c2           # edge to child chosen: merge, sign -1
                nxt[(r1, merge_part(p1, p2 + (r2,)))] += c1 * c2       # edge not chosen: close child's root comp
        cur = {k: v for k, v in nxt.items() if v}
    memo[key] = cur
    return cur

def combine(maps):
    # merge a run of root components joined by chosen cycle edges (sign handled by caller)
    cur = {(0, ()): 1}
    for M in maps:
        nxt = defaultdict(int)
        for (r1, p1), c1 in cur.items():
            for (r2, p2), c2 in M.items():
                nxt[(r1 + r2, merge_part(p1, p2))] += c1 * c2
        cur = nxt
    return cur

def csf(seq):
    c = len(seq); maps = [tree_map(a, i) for (a, i) in seq]; total = defaultdict(int)
    for mask in range(1 << c):
        chosen = [(mask >> j) & 1 for j in range(c)]   # edge j joins cycle vertex j and j+1
        k = sum(chosen)
        if k == c:
            groups = [list(range(c))]
        else:
            start = next(j for j in range(c) if not chosen[j]) + 1
            groups = []; g = []
            for t in range(c):
                v = (start + t) % c; g.append(v)
                if not chosen[v]: groups.append(g); g = []
        cur = {((), ): 1}
        part_maps = []
        res = {(): (-1) ** k}
        for g in groups:
            M = combine([maps[v] for v in g]); nxt = defaultdict(int)
            for p0, c0 in res.items():
                for (r, p), cc in M.items():
                    nxt[merge_part(p0, p + (r,))] += c0 * cc
            res = nxt
        for p, v in res.items(): total[p] += v
    return frozenset((p, v) for p, v in total.items() if v)

def invariants(seq):
    c = len(seq); edges = [(j, (j + 1) % c) for j in range(c)]; nxt = c
    exec_edges = []
    def expand(s, i, root):
        nonlocal nxt
        for (cs, ci) in trees[s][i]:
            v = nxt; nxt += 1; edges.append((root, v)); expand(cs, ci, v)
    for j, (a, i) in enumerate(seq): expand(a, i, j)
    deg = defaultdict(int)
    for u, v in edges: deg[u] += 1; deg[v] += 1
    internal = sum(1 for u, v in edges if deg[u] > 1 and deg[v] > 1)
    return (tuple(sorted(deg.values())), sum(1 for (a, i) in seq if a > 1), internal)

if __name__ == '__main__':
    n = NMAX; groups = defaultdict(list); count = 0
    for comp in compositions(n, C):
        for choice in itertools.product(*[range(len(trees[a])) for a in comp]):
            seq = tuple(zip(comp, choice))
            if canon(seq) != seq: continue
            groups[csf(seq)].append(seq); count += 1
    coll = [g for g in groups.values() if len(g) > 1]
    bad = [g for g in coll if len({invariants(s) for s in g}) > 1]
    out = dict(n=n, cycle=C, graphs=count, distinct_csf=len(groups), collision_classes=len(coll),
               collision_classes_with_differing_invariants=len(bad), examples_bad=[[repr(s) for s in g] for g in bad[:5]],
               examples_collision=[[repr(s) for s in g] for g in coll[:3]], invariants_bad=[[invariants(s) for s in g] for g in bad[:3]])
    json.dump(out, open(sys.argv[3], 'w'), indent=1)
    print(n, C, count, 'distinct', len(groups), 'collisions', len(coll), 'bad', len(bad))
