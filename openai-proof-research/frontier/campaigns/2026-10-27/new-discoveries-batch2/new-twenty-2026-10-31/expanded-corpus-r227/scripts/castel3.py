"""364839 scouting: random lattice 3-polytopes; report Castelnuovo ones (6 vol = 3c + 2b - 7, c >= 1)
and any with c >= 2 and b > 3c + 8 (would contradict Hamano-Sainose-Hibi Conjecture 3.3 at d = 3).
Usage: castel3.py SEED SAMPLES BOX NPTS"""
import sys, random, itertools, json
from fractions import Fraction

def sub(a, b): return (a[0]-b[0], a[1]-b[1], a[2]-b[2])
def cross(a, b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def dot(a, b): return a[0]*b[0]+a[1]*b[1]+a[2]*b[2]

def hull_facets(P):
    """facets as (normal n, offset k) with n.x <= k for all points; via brute force over triples"""
    F = set()
    for a, b, c in itertools.combinations(P, 3):
        n = cross(sub(b, a), sub(c, a))
        if n == (0, 0, 0): continue
        k = dot(n, a)
        s = [dot(n, p) - k for p in P]
        if all(x <= 0 for x in s): pass
        elif all(x >= 0 for x in s): n = (-n[0], -n[1], -n[2]); k = -k
        else: continue
        from math import gcd
        g = gcd(gcd(abs(n[0]), abs(n[1])), gcd(abs(n[2]), abs(k)))
        F.add((n[0]//g, n[1]//g, n[2]//g, k//g))
    return [((f[0], f[1], f[2]), f[3]) for f in F]

def analyse(P):
    F = hull_facets(P)
    if not F: return None
    # full-dimensional check: some point strictly inside some facet's halfspace
    if all(all(dot(n, p) == k for p in P) for n, k in F): return None
    lo = [min(p[i] for p in P) for i in range(3)]; hi = [max(p[i] for p in P) for i in range(3)]
    b = c = 0; pts = []
    for x in range(lo[0], hi[0]+1):
        for y in range(lo[1], hi[1]+1):
            for z in range(lo[2], hi[2]+1):
                q = (x, y, z); s = [k - dot(n, q) for n, k in F]
                if min(s) < 0: continue
                if min(s) == 0: b += 1
                else: c += 1
                pts.append(q)
    # normalized volume: cone from a vertex over facets; facet polygon fan-triangulated
    verts = [p for p in set(P) if sum(1 for n, k in F if dot(n, p) == k) >= 3]
    v0 = verts[0]; vol6 = 0
    for n, k in F:
        if dot(n, v0) == k: continue
        fv = [p for p in verts if dot(n, p) == k]
        # order fv around centroid in facet plane
        cx = [Fraction(sum(p[i] for p in fv), len(fv)) for i in range(3)]
        u = sub(fv[0], fv[0]); u = tuple(Fraction(fv[0][i]) - cx[i] for i in range(3))
        w = cross(n, u)
        import math
        fv.sort(key=lambda p: math.atan2(float(dot(w, tuple(p[i]-cx[i] for i in range(3)))), float(dot(u, tuple(p[i]-cx[i] for i in range(3))))))
        for i in range(1, len(fv)-1):
            vol6 += abs(dot(sub(fv[0], v0), cross(sub(fv[i], v0), sub(fv[i+1], v0))))
    return b, c, vol6, len(verts)

if __name__ == '__main__':
    seed, S, M, K = map(int, sys.argv[1:5])
    rng = random.Random(seed); cast = {}; viol = []
    for _ in range(S):
        P = [tuple(rng.randint(-M, M) for _ in range(3)) for _ in range(K)]
        r = analyse(P)
        if not r: continue
        b, c, v6, nv = r
        if c >= 1 and v6 == 3*c + 2*b - 7:
            key = (b, c); cast[key] = cast.get(key, 0) + 1
            if c >= 2 and b > 3*c + 8:
                viol.append({'P': P, 'b': b, 'c': c, 'vol6': v6}); print('VIOLATION', json.dumps(viol[-1]), flush=True)
    print(json.dumps({'seed': seed, 'samples': S, 'box': M, 'npts': K,
                      'castelnuovo_bc_counts': {f'{b},{c}': v for (b, c), v in sorted(cast.items())}, 'violations': len(viol)}))
