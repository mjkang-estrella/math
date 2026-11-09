"""Exact chi'_S for all Shannon triangles (multiplicities A,B,C >= 1, <= M) under readings deg / sub / subnl
(see sedge3.py). Characterisation by type.  A colour class of a triangle is a count triple (a,b,c) on bouquets xy, xz, yz.
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
S2 = {(p[0]+q[0], p[1]+q[1], p[2]+q[2]) for p in V for q in V if max(p[0]+q[0], p[1]+q[1], p[2]+q[2]) <= M}
S3 = {(p[0]+q[0], p[1]+q[1], p[2]+q[2]) for p in S2 for q in V if max(p[0]+q[0], p[1]+q[1], p[2]+q[2]) <= M}
out = {}
for A in range(1, M + 1):
  for B in range(A, M + 1):
    for C in range(B, M + 1):
      ty = str(tuple(sorted((2 - (m % 2) for m in (A, B, C)), reverse=True)))
      chi4 = (A, B, C) not in S3
      out.setdefault(ty, {'chi4': [], 'le3': []})['chi4' if chi4 else 'le3'].append((A, B, C))
for ty, d in sorted(out.items()):
  print(ty, 'chi>=4:', len(d['chi4']), ' <=3:', len(d['le3']))
  if ty in ('(2, 1, 1)', '(2, 2, 1)'):
    print('   <=3 with A>=3:', [t for t in d['le3'] if t[0] >= 4][:40])
    print('   min A among chi4:', min(t[0] for t in d['chi4']) if d['chi4'] else None)
