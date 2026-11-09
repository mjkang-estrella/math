"""Exact chi'_S for all Shannon triangles (multiplicities A,B,C >= 1, <= M) under readings deg / sub / subnl
(see sedge3.py).  A colour class of a triangle is a count triple (a,b,c) on bouquets xy, xz, yz.
usage: sedge_tri.py mode M"""
import sys, itertools, json
mode, M = sys.argv[1], int(sys.argv[2])
def valid(a, b, c):
    dx, dy, dz = a + b, a + c, b + c
    D = (dx, dy, dz)
    if any(not (d == 0 or d == 2 or d % 2) for d in D): return False
    if mode == 'deg': return True
    # components: vertices with positive degree, connected via positive bouquets
    E = [(0, 1, a), (0, 2, b), (1, 2, c)]
    vs = [v for v in range(3) if D[v] > 0]
    # component structure of a triangle: union-find
    par = list(range(3))
    def f(x):
        while par[x] != x: x = par[x]
        return x
    for u, v, m in E:
        if m: par[f(u)] = f(v)
    comps = {}
    for v in vs: comps.setdefault(f(v), []).append(v)
    if any(not any(D[v] % 2 for v in cp) for cp in comps.values()): return False
    if mode == 'subnl':
        # a 2-vertex whose two edges go to the same neighbour forms a thread returning to that neighbour
        # (or, if the neighbour is also a 2-vertex, a digon component, already excluded).  Longer threads
        # through two 2-vertices: x-y-z-x with dy=dz=2 and a path of 2-vertices from x back to x.
        for v in range(3):
            if D[v] == 2:
                nb = [m for (p, q, m) in E for w in (p, q) if w == v]
                inc = [(p, q, m) for (p, q, m) in E if v in (p, q) and m > 0]
                if len(inc) == 1 and inc[0][2] == 2:   # both edges to one neighbour w
                    w = inc[0][0] if inc[0][1] == v else inc[0][1]
                    if D[w] % 2: return False          # subdivided loop at odd vertex w
        # two adjacent 2-vertices y,z with one edge each to x and one edge yz: thread x-y-z-x (loop at x)
        for x in range(3):
            y, z = [v for v in range(3) if v != x]
            if D[y] == 2 and D[z] == 2 and D[x] % 2:
                exy = [m for (p, q, m) in E if {p, q} == {x, y}][0]; exz = [m for (p, q, m) in E if {p, q} == {x, z}][0]
                eyz = [m for (p, q, m) in E if {p, q} == {y, z}][0]
                if exy == 1 and exz == 1 and eyz == 1: return False
    return True
V = [(a, b, c) for a in range(M + 1) for b in range(M + 1) for c in range(M + 1) if valid(a, b, c)]
S1 = set(V)
S2 = {(p[0] + q[0], p[1] + q[1], p[2] + q[2]) for p in V for q in V if p[0] + q[0] <= M and p[1] + q[1] <= M and p[2] + q[2] <= M}
S3 = {(p[0] + q[0], p[1] + q[1], p[2] + q[2]) for p in S2 for q in V if p[0] + q[0] <= M and p[1] + q[1] <= M and p[2] + q[2] <= M}
res = {'chi<=1': 0, 'chi=2': 0, 'chi=3': 0, 'chi>=4': 0}; four = []; typ = {}
for A in range(1, M + 1):
    for B in range(A, M + 1):
        for C in range(B, M + 1):
            t = (A, B, C)
            if t in S1: res['chi<=1'] += 1
            elif t in S2: res['chi=2'] += 1
            elif t in S3: res['chi=3'] += 1
            else:
                res['chi>=4'] += 1; four.append(t)
                ty = tuple(sorted((2 - (m % 2) for m in t), reverse=True))
                typ[str(ty)] = typ.get(str(ty), 0) + 1
print(json.dumps(dict(mode=mode, M=M, counts=res, chi4_by_type=typ, chi4_smallest=sorted(four, key=lambda t: (sum(t), t))[:25])))
