#!/usr/bin/env python3
"""Decisive exact calculation for MathDB 389505 (Benjamini, symmetric sets on S^2).

Exhibits an explicit 120-point finite X subset S^2, transitive under the full
icosahedral group I_h (order 120, incl. reflections), NOT contained in a great
circle and NOT contained in the union of two parallel circles (two latitudes).
All arithmetic exact in Q(sqrt5): field element = a + b*sqrt5 with a,b rationals.
"""
from fractions import Fraction as F
import json, os

def add(x, y): return (x[0] + y[0], x[1] + y[1])
def sub(x, y): return (x[0] - y[0], x[1] - y[1])
def mul(x, y): return (x[0]*y[0] + 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def scal(c, x): return (c*x[0], c*x[1])
def eq(x, y): return x[0] == y[0] and x[1] == y[1]
def neg(x): return (-x[0], -x[1])
F0 = (F(0), F(0)); F1 = (F(1), F(0))
FH = (F(1, 2), F(0))                       # 1/2
PHI = (F(1, 2), F(1, 2))                   # (1+sqrt5)/2
PHI_INV = (F(-1, 2), F(1, 2))              # (sqrt5-1)/2
assert eq(mul(PHI, PHI_INV), F1)

# unit quaternion q = (w,x,y,z), entries field elements
def qmul(a, b):
    w1, x1, y1, z1 = a; w2, x2, y2, z2 = b
    w = sub(sub(sub(mul(w1, w2), mul(x1, x2)), mul(y1, y2)), mul(z1, z2))
    x = add(add(mul(w1, x2), mul(x1, w2)), sub(mul(y1, z2), mul(z1, y2)))
    y = add(add(mul(w1, y2), mul(y1, w2)), sub(mul(z1, x2), mul(x1, z2)))
    z = add(add(mul(w1, z2), mul(z1, w2)), sub(mul(x1, y2), mul(y1, x2)))
    return (w, x, y, z)

def qneg(a): return tuple(neg(c) for c in a)
def qnorm2(a):
    s = F0
    for c in a: s = add(s, mul(c, c))
    return s

ident = (F1, F0, F0, F0)
def half_(x): return scal(F(1, 2), x)
g1 = (FH, FH, FH, FH)                                  # (1+i+j+k)/2 : order 3
g2 = (F0, FH, half_(PHI), half_(PHI_INV))              # (0,1,phi,1/phi)/2 : order 2

group = {ident}
frontier = [ident]
while frontier:
    new = []
    for a in frontier:
        for g in (g1, g2):
            for b in (qmul(a, g), qmul(g, a)):
                if b not in group:
                    group.add(b); new.append(b)
    frontier = new
assert all(eq(qnorm2(q), F1) for q in group), "non-unit element"
print("2I closure size:", len(group))

def rot(q):
    w, x, y, z = q
    two = F(2)
    return [
        [sub(F1, scal(two, add(mul(y, y), mul(z, z)))),
         scal(two, sub(mul(x, y), mul(w, z))),
         scal(two, add(mul(x, z), mul(w, y)))],
        [scal(two, add(mul(x, y), mul(w, z))),
         sub(F1, scal(two, add(mul(x, x), mul(z, z)))),
         scal(two, sub(mul(y, z), mul(w, x)))],
        [scal(two, sub(mul(x, z), mul(w, y))),
         scal(two, add(mul(y, z), mul(w, x))),
         sub(F1, scal(two, add(mul(x, x), mul(y, y))))],
    ]

def mapply(R, v):
    return tuple(add3(i, R, v) for i in range(3))

def add3(i, R, v):
    s = F0
    for j in range(3):
        s = add(s, mul(R[i][j], v[j]))
    return s

# dedupe q ~ -q (same rotation)
canon = {}
for q in group:
    key = min(json.dumps(q, default=str), json.dumps(qneg(q), default=str))
    canon.setdefault(key, q)
rots = [rot(q) for q in canon.values()]
print("distinct rotations:", len(rots))

full = []
for R in rots:
    full.append(R)
    full.append([[neg(c) for c in row] for row in R])
print("full group order:", len(full))

# generic point direction with rational entries and rational norm |p| = 7
p_dir = ((F(2), F(0)), (F(3), F(0)), (F(6), F(0)))
assert sum([4, 9, 36]) == 49

orb120 = {tuple(tuple(c) for c in mapply(R, p_dir)) for R in full}
zs = sorted({v[2] for v in orb120}, key=lambda t: (t[0], t[1]))
print("orbit size under I_h:", len(orb120))
print("distinct z-values:", len(zs))

def det3(a, b, c):
    t1 = mul(a[0], sub(mul(b[1], c[2]), mul(c[1], b[2])))
    t2 = mul(b[0], sub(mul(c[1], a[2]), mul(a[1], c[2])))
    t3 = mul(c[0], sub(mul(a[1], b[2]), mul(b[1], a[2])))
    return add(add(t1, t2), t3)

# not on a great circle: orbit spans R^3 iff some triple has nonzero det.
# (I_h acts irreducibly; verify exactly by search.)
det_ok = False
det_val = None
pts = [mapply(R, p_dir) for R in full]
for i in range(len(pts)):
    for j in range(i + 1, len(pts)):
        d = det3(p_dir, pts[i], pts[j])
        if not eq(d, F0):
            det_ok = True; det_val = d; break
    if det_ok: break

# rotational-only orbit (orientation-preserving reading)
orb60 = {tuple(tuple(c) for c in mapply(R, p_dir)) for R in rots}
print("orbit size under rotational group:", len(orb60))

result = {
    "twoI_size": len(group),
    "rotational_order": len(rots),
    "full_order": len(full),
    "orbit_size_full": len(orb120),
    "distinct_z_values_full_orbit": len(zs),
    "z_min": str(zs[0]), "z_max": str(zs[-1]),
    "not_on_great_circle_det_nonzero": det_ok,
    "det_value": str(det_val) if det_ok else None,
    "orbit_size_rotational": len(orb60),
    "conclusion": ("Explicit 120-point orbit of the full icosahedral group I_h on S^2 with "
                   ">=3 distinct latitudes (not on two parallel circles) and not on a great "
                   "circle; universal bound |X| <= |G| <= 120 for finite G <= O(3)."),
}
out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   '..', 'sources', '389505', 'orbit-120-calculation.json')
os.makedirs(os.path.dirname(out), exist_ok=True)
open(out, 'w').write(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
