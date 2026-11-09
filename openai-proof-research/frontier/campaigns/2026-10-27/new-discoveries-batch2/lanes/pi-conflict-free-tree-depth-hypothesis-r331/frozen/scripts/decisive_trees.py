#!/usr/bin/env python3
"""Decisive calculation for r320 proposal 338062 (arXiv:1712.10010v2 Conjecture 3.6:
D(T) < 2*cfc(T) for every tree T).

Enumerate all unlabeled trees on <= 9 vertices (via Prufer sequences, deduplicated),
compute D(T) exactly (min iterations of Algorithm 1 over balanced-edge tie-breaking,
memoized on canonical subtree) and cfc(T) by exhaustive search, and look for a tree
with D(T) >= 2*cfc(T). Writes work/decisive-trees.json.
"""
import json, os, itertools
from functools import lru_cache

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WORK = os.path.join(LANE, "work")

def tree_from_prufer(code):
    n = len(code) + 2
    deg = [1] * (n + 1)
    for c in code: deg[c] += 1
    edges = []
    for i, c in enumerate(code):
        rest = code[i + 1:]
        # smallest leaf not occurring in the remaining code
        leaf = next(v for v in range(1, n + 1) if deg[v] == 1 and v not in rest)
        edges.append((min(leaf, c), max(leaf, c)))
        deg[leaf] -= 1
        deg[c] -= 1
    rem = [v for v in range(1, n + 1) if deg[v] == 1]
    edges.append((min(rem), max(rem)))
    return edges

def canon(n, edges):
    """Canonical string of an unlabeled tree via iterative leaf-stripping."""
    if n == 1: return "1"
    adj = [[] for _ in range(n + 1)]
    for a, b in edges: adj[a].append(b); adj[b].append(a)
    # find all leaves, strip layers computing labels
    labels = {v: "1" for v in range(1, n + 1)}
    # simple approach: AHU-like from a fixed root is not canonical; use
    # centroid + sorted subtree encodings from both centroid roots
    def subtree_enc(root, parent):
        encs = sorted(subtree_enc(c, root) for c in adj[root] if c != parent)
        return "(" + "".join(encs) + ")"
    # centroids
    deg = [len(adj[v]) for v in range(n + 1)]
    leaves = [v for v in range(1, n + 1) if deg[v] <= 1]
    removed = 0; cnt = n
    touch = deg[:]
    stack = list(leaves); cut = [False] * (n + 1); last = []
    while cnt > 2:
        nl = []
        for v in stack:
            if cut[v]: continue
            cut[v] = True; cnt -= 1
            for w in adj[v]:
                touch[w] -= 1
                if touch[w] <= 1 and not cut[w]: nl.append(w)
        stack = [v for v in nl if not cut[v]]
        last = stack[:]
    cents = [v for v in range(1, n + 1) if not cut[v]]
    encs = sorted(subtree_enc(c, 0) for c in cents)
    return f"{n}:" + "".join(encs)

def components_after_removal(n, edges, e):
    """Return (sizeA, canonA, sizeB, canonB) for tree minus edge e, or None."""
    adj = [[] for _ in range(n + 1)]
    for a, b in edges:
        if (a, b) == e: continue
        adj[a].append(b); adj[b].append(a)
    seen = {1}; stack = [1]; comp = [1]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in seen: seen.add(w); stack.append(w); comp.append(w)
    if len(seen) == n: return None
    def sub_edges(nodes):
        ns = set(nodes); idx = {v: i + 1 for i, v in enumerate(sorted(ns))}
        ee = []
        for a, b in edges:
            if a in ns and b in ns and (a, b) != e: ee.append((idx[a], idx[b]))
        return len(ns), canon(len(ns), ee), ee
    rest = [v for v in range(1, n + 1) if v not in seen]
    A = sub_edges(sorted(seen)); B = sub_edges(rest)
    return A, B

@lru_cache(maxsize=None)
def depth_canon(key):
    """min iterations of Algorithm 1 over balanced-edge tie-breaking."""
    n, edges_s = key
    edges = eval(edges_s)
    if n == 1: return 0
    # size difference for each edge
    diffs = []
    comps = {}
    for e in edges:
        r = components_after_removal(n, edges, e)
        comps[e] = r
        diffs.append(abs(r[0][0] - r[1][0]))
    mind = min(diffs)
    best = None
    for e, d in zip(edges, diffs):
        if d != mind: continue
        A, B = comps[e]
        # A = (sizeA, canonA, edgesA); note sub_edges returns (len, canon, edges)
        dA = depth_canon((A[0], repr(A[2])))
        dB = depth_canon((B[0], repr(B[2])))
        v = 1 + max(dA, dB)
        best = v if best is None else min(best, v)
    return best

def D_of_tree(n, edges):
    return depth_canon((n, repr(edges)))

def cfc_bruteforce(n, edges, max_k=5):
    """min colors k such that every path has a unique color (tree)."""
    m = len(edges)
    # enumerate all pairs' paths via tree structure
    adj = [[] for _ in range(n + 1)]
    for i, (a, b) in enumerate(edges): adj[a].append((b, i)); adj[b].append((a, i))
    paths = []
    for s in range(1, n + 1):
        # BFS paths from s
        stack = [(s, frozenset())]
        seen = {s}
        # paths in a tree: unique; enumerate via DFS from each vertex
        def dfs(v, parent, es):
            for w, i in adj[v]:
                if w == parent: continue
                paths.append(frozenset(es | {i}))
                dfs(w, v, es | {i})
        dfs(s, 0, frozenset())
    paths = set(paths)
    lo = max(1, (n - 1).bit_length())  # >= ceil(log2 n)
    for k in range(lo, max_k + 1):
        for col in itertools.product(range(k), repeat=m):
            ok = True
            for p in paths:
                cc = [col[i] for i in p]
                if all(cc.count(c) != 1 for c in set(cc)): ok = False; break
            if ok: return k
    return None

results = {}
worst = []
for n in range(2, 10):
    seen = set(); count = 0; bad = []
    for code in itertools.product(range(1, n + 1), repeat=n - 2):
        edges = tree_from_prufer(list(code))
        c = canon(n, edges)
        if c in seen: continue
        seen.add(c); count += 1
        D = D_of_tree(n, edges)
        Delta = max(sum(1 for a, b in edges if a == v) + sum(1 for a, b in edges if b == v) for v in range(1, n + 1))
        if D < 2 * Delta:
            results[c] = {"n": n, "D": D, "cfc": f">={Delta}", "skip": "D<2*Delta"}
            continue
        cfc = cfc_bruteforce(n, edges, max_k=min(4, D // 2))
        results[c] = {"n": n, "D": D, "cfc": cfc if cfc is not None else f">{D//2}"}
        if cfc is not None and D >= 2 * cfc: bad.append({"canon": c, "D": D, "cfc": cfc})
    print(f"n={n}: {count} unlabeled trees, counterexamples: {len(bad)}", flush=True)
    if bad: worst.extend(bad)

with open(os.path.join(WORK, "decisive-trees.json"), "w") as f:
    json.dump({"counterexamples_D_ge_2cfc": worst,
               "max_D_over_cfc_numeric": max(([v["D"] / v["cfc"], k] for k, v in results.items() if isinstance(v["cfc"], int)), default=None),
               "all": results}, f)
print("DONE; counterexamples:", len(worst))
