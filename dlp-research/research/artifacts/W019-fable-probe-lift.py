#!/usr/bin/env python3
"""Audit probe (NOT a repaired prototype). Imports the untouched W019 prototype
functions and tests which lift matters for the p=61 failure:
 (A) perturb the POINT lift x -> x + k*p (what the report says was tried),
 (B) perturb the CURVE lift b -> b + k*p mod p^2 (what the report never tried).
Also checks whether the integer lift of y^2=x^3+2 behaves as the canonical-lift
failure case predicted by the trace-one method's E_2 obstruction."""
import sys, time
sys.argv = ["proto"]
import importlib.util, io, contextlib
spec = importlib.util.spec_from_file_location("proto", "/tmp/w019-audit/proto.py")
proto = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(proto)   # runs its own demo; output suppressed

T0 = time.perf_counter()

def smart_dlp_lift(G, Q, a, b, p, bl, xshiftG=0):
    """Same algorithm as proto.smart_dlp but with explicit curve lift bl (b mod p^2)
    and optional x-shift of the lifted G by multiples of p (point-lift change)."""
    M = p * p
    assert bl % p == b % p
    # Hensel lift of y for x fixed, on curve y^2 = x^3 + a x + bl over Z/p^2
    def hensel(x, y):
        y0 = y % p
        f = (pow(x, 3, M) + a * x + bl) % M
        delta = (f - y0 * y0) % M
        assert delta % p == 0
        t = ((delta // p) * proto.inv(2 * y0, p)) % p
        Y = (y0 + t * p) % M
        assert (Y * Y - f) % M == 0
        return x % M, Y
    Gx, Gy = hensel((G[0] + xshiftG * p) % M, G[1])
    Qx, Qy = hensel(Q[0], Q[1])
    JP = proto.jac_mul(p, (Gx, Gy, 1), a, M)
    JQ = proto.jac_mul(p, (Qx, Qy, 1), a, M)
    tP = proto.formal_t(JP, p)
    tQ = proto.formal_t(JQ, p)
    if tP is None or tQ is None or tP % p != 0 or (tP // p) % p == 0:
        return None, tP, tQ, JP
    return ((tQ // p) * proto.inv((tP // p) % p, p)) % p, tP, tQ, JP

p, a, b = 61, 0, 2
assert proto.point_count(a, b, p) == p
pts = [pt for pt in proto.all_affine(a, b, p) if pt[1] % p != 0]
G = pts[0]
secrets = [1, 2, 3, 7, 11, 30]
Qs = {m: proto.aff_mul(m, G, a, p) for m in secrets}

# (A) point-lift perturbation, curve lift fixed at integer b=2
okA = 0
for k in range(p):
    m, tP, tQ, JP = smart_dlp_lift(G, Qs[7], a, b, p, b, xshiftG=k)
    okA += (m == 7)
print("A: point x-lift shifts k=0..60 with curve lift b=2: successes", okA, "/", p,
      "example k=0 JP=", tuple(c % (p*p) for c in smart_dlp_lift(G, Qs[7], a, b, p, b)[3]))

# (B) curve-lift perturbation b -> 2 + k*61
resB = []
for k in range(p):
    bl = (b + k * p) % (p * p)
    got = [smart_dlp_lift(G, Qs[m], a, b, p, bl)[0] == m for m in secrets]
    resB.append(sum(got))
print("B: curve lift b=2+61k, k=0..60: per-k successes out of 6:", resB)
print("   k with all 6 correct:", sum(1 for r in resB if r == 6), "; k with 0 correct:",
      [k for k, r in enumerate(resB) if r == 0])

# (C) same two experiments on the j!=0 anomalous curve (43,4,2) for contrast
p2, a2, b2 = 43, 4, 2
pts2 = [pt for pt in proto.all_affine(a2, b2, p2) if pt[1] % p2 != 0]
G2 = pts2[0]
Q2 = proto.aff_mul(7, G2, a2, p2)
failC = [k for k in range(p2) if smart_dlp_lift(G2, Q2, a2, b2, p2, (b2 + k * p2) % (p2*p2))[0] != 7]
print("C: (43,4,2) curve lifts b=2+43k failing:", failC)

# (D) j-invariant check: is (61,0,2) j=0 ? and does a j=0 lift a=0 fail for every b lift? try a-lift instead
failD = [k for k in range(p) if smart_dlp_lift(G, Qs[7], (0 + k * p), b, p, b)[0] != 7]
print("D: (61,0,2) a-lift a=0+61k failing k:", failD)

print("ops", proto.OPS, "sec", round(time.perf_counter() - T0, 3))
