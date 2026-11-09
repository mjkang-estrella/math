"""Exhaustive F2-quadratic search over ALL subsets of a spherical universe U
(no three collinear points, verified).  For S subset U:
   n_S(l) = |S| - #{pairs of S with direction l}.
Line-all-even <=> |S| even and, for every direction class c of U,
   sum_{ {a,b} in c } x_a x_b = 0 (mod 2).
Every solution is reported with its affine dimension; only affine dim 3 would
be a candidate (to be re-verified exactly).  Float direction keys (6 digits);
support/exploration only.  Usage: sphere_exhaust.py NAME"""
import sys, os, json, itertools, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lp import _fkey

phi = (1 + 5 ** 0.5) / 2


def unit(v):
    v = np.array(v, float)
    return v / np.linalg.norm(v)


def ring(n, z, off=0.0):
    r = math.sqrt(1 - z * z)
    return [(r * math.cos(2 * math.pi * (i + off) / n), r * math.sin(2 * math.pi * (i + off) / n), z) for i in range(n)]


def evenperm_orbit(v, allsigns=False):
    pts = set()
    for p in [(0, 1, 2), (1, 2, 0), (2, 0, 1)] + ([] if not allsigns else []):
        w = [v[p[0]], v[p[1]], v[p[2]]]
        for s in itertools.product([1, -1], repeat=3):
            if not allsigns and s[0] * s[1] * s[2] != 1:
                continue
            pts.add(tuple(round(a * b, 12) for a, b in zip(s, w)))
    return [tuple(unit(p)) for p in pts]


def td_orbit(v):
    pts = set()
    for p in itertools.permutations(range(3)):
        w = [v[p[0]], v[p[1]], v[p[2]]]
        for s in itertools.product([1, -1], repeat=3):
            if s[0] * s[1] * s[2] == 1:
                pts.add(tuple(round(a * b, 12) for a, b in zip(s, w)))
    return [tuple(unit(p)) for p in pts]


ico = [tuple(unit(p)) for p in evenperm_orbit((0, 1, phi), allsigns=True)]
U = {
    'trunc_tetra_12': td_orbit((3, 1, 1)),
    'icosahedron_12': ico,
    'cubocta_12': [tuple(unit(p)) for p in td_orbit((1, 1, 0)) + td_orbit((1, -1, 0))],
    'cube_octa_14': [tuple(unit(p)) for p in set(itertools.product([1, -1], repeat=3))] +
                    [tuple(s * e for e in v) for v in np.eye(3) for s in (1, -1)],
    'rings_6_6_6': ring(6, 0) + ring(6, 0.6, 0.5) + ring(6, -0.6, 0.5),
    'rings_8_6_6': ring(8, 0) + ring(6, 0.5) + ring(6, -0.5),
    'rings_7_7_7': ring(7, 0) + ring(7, 0.6) + ring(7, -0.6, 0.5),
    'rings_9_6_6': ring(9, 0) + ring(6, 0.5) + ring(6, -0.5, 0.5),
    'rings_10_5_5': ring(10, 0) + ring(5, 0.5) + ring(5, -0.5, 0.5),
    'rings_5_5_5_5': ring(5, 0.3) + ring(5, -0.3, 0.5) + ring(5, 0.8, 0.5) + ring(5, -0.8),
    'P13_control': ring(13, 0),
    'P15_control': ring(15, 0),
    'P16_control': ring(16, 0),
    'rings_13_4_4': ring(13, 0) + ring(4, 0.6) + ring(4, -0.6, 0.5),
    'rings_15_3_3': ring(15, 0) + ring(3, 0.6) + ring(3, -0.6, 0.5),
    'rings_13_5_4': ring(13, 0) + ring(5, 0.6) + ring(4, -0.6, 0.5),
    'rings_15_6': ring(15, 0) + ring(6, 0.7, 0.25),
    'rings_13_8': ring(13, 0) + ring(8, 0.5, 0.1),
    'rings_12_4_4': ring(12, 0) + ring(4, 0.6) + ring(4, -0.6, 0.5),
}
name = sys.argv[1]
pts = [np.array(p, float) for p in U[name]]
N = len(pts)
# verify no three collinear
lines = {}
for i, j in itertools.combinations(range(N), 2):
    for k in range(N):
        if k in (i, j):
            continue
        if np.linalg.norm(np.cross(pts[j] - pts[i], pts[k] - pts[i])) < 1e-9:
            raise SystemExit('collinear triple')
classes = {}
for i, j in itertools.combinations(range(N), 2):
    classes.setdefault(_fkey(tuple(pts[j] - pts[i]), 6), []).append((i, j))
cl = list(classes.values())
x = np.arange(1 << N, dtype=np.uint32)
bad = (np.bitwise_count(x) & 1).astype(np.uint8) if hasattr(np, 'bitwise_count') else None
if bad is None:
    bad = np.zeros(1 << N, np.uint8)
    for b in range(N):
        bad ^= ((x >> b) & 1).astype(np.uint8)
bits = [((x >> b) & 1).astype(np.uint8) for b in range(N)]
del x
for c in cl:
    par = np.zeros(1 << N, np.uint8)
    for i, j in c:
        par ^= bits[i] & bits[j]
    bad |= par
sol = np.nonzero(bad == 0)[0]
dims = {}
spanning = []
planar = []
for s in sol:
    S = [pts[b] for b in range(N) if (int(s) >> b) & 1]
    if not S:
        dims['empty'] = dims.get('empty', 0) + 1
        continue
    d = int(np.linalg.matrix_rank(np.array(S) - S[0], tol=1e-7))
    dims[d] = dims.get(d, 0) + 1
    if d == 2 and len(planar) < 3:
        planar.append(''.join('1' if (int(s) >> b) & 1 else '0' for b in range(N)))
    if d == 3 and len(spanning) < 5:
        spanning.append([list(map(float, p)) for p in S])
print(json.dumps({'universe': name, 'points': N, 'classes': len(cl),
                  'singleton_classes': sum(1 for c in cl if len(c) == 1),
                  'solutions_by_affine_dim': {str(k): v for k, v in dims.items()},
                  'planar_examples': planar, 'spanning_examples': spanning}))
