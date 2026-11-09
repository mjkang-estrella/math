"""Independent exact checker (r618) for MathDB 338366 / BRT Conjecture 4.1, p=q=2.

Graph T = Bai-Lu-Yau arXiv:2103.00941v2 Theorem 11 / Figure 35, reconstructed from
the Type C labels (Figure 33) and the Case 1a text (see review.md for the line-by-line
reconstruction).  Also re-checks the r602 AGL(1,5) Cayley candidate from its literal
generators (upstream scripts are not imported or executed).

Exact arithmetic only: lazy measures with rational masses k/N are split into N unit
atoms; W1 equals (1/N) * minimum-cost assignment (transportation polytope with integral
supplies has an integral optimum), solved exactly by bitmask DP.
Usage: python3 -I -B check_bly35.py OUT.json
"""
import json, sys, itertools
from fractions import Fraction as F
from collections import deque

TYPE_C = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(5,6),(6,1),(1,7),(7,8),(8,2),
          (2,9),(9,10),(10,3),(3,11),(11,12),(12,4),(4,13),(13,14),(14,0)]
# Case 1a text: 12~7; 12~16~15~7; 14~9; 14~15; 6~11; 6~17~18~11; 9~17~15;
# 5~16; 5~10; 8~13; 8~18; 18~19~13; 19~16; 10~19 (forced 4th neighbours; see review).
CASE_1A = [(12,7),(12,16),(16,15),(15,7),(14,9),(14,15),(6,11),(6,17),(17,18),
           (18,11),(9,17),(17,15),(5,16),(5,10),(8,13),(8,18),(18,19),(19,13),
           (19,16),(10,19)]
FIGURE_EXTRA = [(2,17)]          # segment drawn in Figure 35 (makes deg 5), not in text
TEXT_CLAIM_16_18 = [(16,18)]     # sentence "Note 16 ~ 18" (makes deg(18)=5 with 18~19)


def adj_of(n, edges):
    A = {v: set() for v in range(n)}
    for a, b in edges:
        assert a != b
        A[a].add(b); A[b].add(a)
    return {v: sorted(A[v]) for v in A}


def bfs(A, s):
    d = {s: 0}; q = deque([s])
    while q:
        u = q.popleft()
        for w in A[u]:
            if w not in d:
                d[w] = d[u] + 1; q.append(w)
    return d


def units(A, x, center, nb):
    return [x] * center + [v for v in A[x] for _ in range(nb)]


def min_assign(src, dst, D):
    n = len(src); INF = 10 ** 9
    dp = [INF] * (1 << n); dp[0] = 0
    for m in range(1 << n):
        if dp[m] == INF: continue
        i = bin(m).count('1')
        if i == n: continue
        for j in range(n):
            if not m >> j & 1:
                c = dp[m] + D[src[i]][dst[j]]
                if c < dp[m | 1 << j]: dp[m | 1 << j] = c
    return dp[(1 << n) - 1]


def kappa(A, D, x, y, center, nb):
    N = center + nb * len(A[x]); assert N == center + nb * len(A[y])
    w = F(min_assign(units(A, x, center, nb), units(A, y, center, nb), D), N)
    return 1 - w / D[x][y]


def c4s(A):
    out = set()
    V = sorted(A)
    for a in V:
        for b in A[a]:
            for c in A[b]:
                if c == a: continue
                for d in A[c]:
                    if d in (a, b): continue
                    if a in A[d]:
                        cyc = (a, b, c, d)
                        k = min(tuple(cyc[i:] + cyc[:i]) for i in range(4))
                        r = tuple(reversed(cyc)); k2 = min(tuple(r[i:] + r[:i]) for i in range(4))
                        out.add(min(k, k2))
    return sorted(out)


def c5s(A):
    out = set()
    for p in itertools.permutations(sorted(A), 5):
        if p[0] != min(p): continue
        if all(p[(i + 1) % 5] in A[p[i]] for i in range(5)):
            r = (p[0],) + tuple(reversed(p[1:]))
            out.add(min(p, r))
    return sorted(out)


def analyse(name, n, edges, full_pairs=True):
    A = adj_of(n, edges)
    degs = sorted(set(len(A[v]) for v in A))
    res = {'name': name, 'n': n, 'm': len(set(tuple(sorted(e)) for e in edges)), 'degrees': degs}
    D = {v: bfs(A, v) for v in A}
    res['connected'] = all(len(D[v]) == n for v in A)
    if degs != [4] or not res['connected']:
        res['regular4_connected'] = False
        return res, A
    res['regular4_connected'] = True
    res['triangles'] = sum(1 for a in A for b in A[a] for c in A[b] if a < b < c and a in A[c])
    C4 = c4s(A)
    res['num_C4'] = len(C4)
    ec = {}
    for cyc in C4:
        for i in range(4):
            e = tuple(sorted((cyc[i], cyc[(i + 1) % 4]))); ec[e] = ec.get(e, 0) + 1
    E = sorted(set(tuple(sorted(e)) for e in edges))
    res['edge_C4_counts'] = sorted(set(ec.get(e, 0) for e in E))
    res['vertex_C4_counts'] = sorted(set(sum(1 for c in C4 if v in c) for v in A))
    res['spheres'] = sorted(set(tuple(sum(1 for w in D[v] if D[v][w] == i)
                                      for i in range(max(D[v].values()) + 1)) for v in A))
    res['S2_by_vertex'] = [sum(1 for w in D[v] if D[v][w] == 2) for v in range(n)]
    # curvature on edges at several idleness values (alpha = center mass)
    edge_k = {}
    for (alpha, center, nb) in [('1/5', 1, 1), ('1/3', 2, 1), ('1/2', 4, 1)]:
        edge_k[alpha] = sorted(set(str(kappa(A, D, x, y, center, nb)) for x, y in E))
    res['edge_kappa_alpha'] = edge_k
    if full_pairs:
        allk = {}
        for x, y in itertools.combinations(range(n), 2):
            allk[(x, y)] = kappa(A, D, x, y, 4, 1)
        res['allpairs_kappa_half_min'] = str(min(allk.values()))
        res['allpairs_kappa_half_values'] = sorted(set(str(v) for v in allk.values()), key=F)
        res['allpairs_count'] = len(allk)
    return res, A


def type_c_check(A):
    ok = all(b in A[a] for a, b in TYPE_C)
    cyc5 = c5s(A)
    C4 = c4s(A)
    def typec(c):
        extra = []
        for i in range(5):
            e = {c[i], c[(i + 1) % 5]}
            cs = [q for q in C4 if e <= set(q) and any({q[j], q[(j + 1) % 4]} == e for j in range(4))]
            if len(cs) != 1: return False
            others = set(cs[0]) - e
            if others & set(c): return False
            extra += list(others)
        return len(set(extra)) == 10
    return {'type_C_labelled_subgraph_present': ok, 'num_C5': len(cyc5),
            'all_C5_type_C': all(typec(c) for c in cyc5)}


def cayley_agl15():
    def comp(u, v): return tuple(u[v[i]] for i in range(5))
    def cyc(*cs):
        p = list(range(5))
        for c in cs:
            for i in range(len(c)): p[c[i]] = c[(i + 1) % len(c)]
        return tuple(p)
    a = cyc((0, 3, 1, 2)); c = cyc((0, 3), (2, 4)); d = cyc((0, 2), (1, 4))
    ainv = tuple(sorted(range(5), key=lambda i: a[i]))
    S = [a, ainv, c, d]
    e = tuple(range(5)); G = {e}; fr = [e]
    while fr:
        g = fr.pop()
        for s in S:
            h = comp(g, s)
            if h not in G: G.add(h); fr.append(h)
    G = sorted(G); idx = {g: i for i, g in enumerate(G)}
    edges = set()
    for g in G:
        for s in S: edges.add(tuple(sorted((idx[g], idx[comp(g, s)]))))
    affine = all(any(all(g[x] == (m * x + t) % 5 for x in range(5)) for m in range(1, 5) for t in range(5)) for g in G)
    return len(G), sorted(edges), affine


def main():
    out = {}
    T = TYPE_C + CASE_1A
    r, A = analyse('BLY_Thm11_Fig35_reconstructed_T', 20, T)
    r.update(type_c_check(A)); r['edges'] = sorted(tuple(sorted(e)) for e in T)
    out['T'] = r
    out['figure_literal_T_plus_2_17'] = analyse('figure_literal', 20, T + FIGURE_EXTRA)[0]
    out['text_literal_T_plus_16_18'] = analyse('text_16_18', 20, T + TEXT_CLAIM_16_18)[0]
    nG, CE, affine = cayley_agl15()
    rc, _ = analyse('r602_AGL15_Cayley', nG, CE)
    rc['group_order'] = nG; rc['all_elements_affine_mod5'] = affine
    out['cayley'] = rc
    out['Z2_spheres_0_3'] = [sum(1 for a in range(-4, 5) for b in range(-4, 5) if abs(a) + abs(b) == i) for i in range(4)]
    json.dump(out, open(sys.argv[1], 'w'), indent=1, sort_keys=True)
    print(json.dumps({k: {kk: v[kk] for kk in v if kk in ('degrees', 'spheres', 'allpairs_kappa_half_min', 'edge_kappa_alpha', 'edge_C4_counts', 'all_C5_type_C')} if isinstance(v, dict) else v for k, v in out.items()}))


if __name__ == '__main__':
    main()
