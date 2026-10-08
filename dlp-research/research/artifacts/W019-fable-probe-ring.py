#!/usr/bin/env python3
"""Audit probe 2 (NOT a repair). Uses untouched W019 prototype functions.
 (1) count Jacobian vs affine ops behind the reported '408 Jacobian additions';
 (2) check whether formal_t's common-p stripping branch is ever reached on the
     tested path, and show it is inert (can only yield t=0 / None);
 (3) show stripping all three Jacobian coords by p is not weighted scaling;
 (4) exhibit a reachable-in-principle invalid branch: jac_add of two distinct
     E_1 points over Z/p^2 silently doubles the first operand;
 (5) sanity: t([2]P1) == 2 t(P1) mod p^2 (log ~ t to this precision);
 (6) confirm a=61 lift solves all six secrets on (61,0,2)."""
import io, contextlib, importlib.util, time
spec = importlib.util.spec_from_file_location("proto", "/tmp/w019-audit/proto.py")
proto = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(proto)
T0 = time.perf_counter()

# (1) op split: re-run the demo's smart_dlp calls only and count
proto.OPS["point_add"] = 0
strip_hits = {"n": 0}
orig_formal_t = proto.formal_t
def formal_t_instr(P, p):
    M = p * p
    X, Y, Z = [c % M for c in P]
    if X % p == 0 and Y % p == 0 and Z % p == 0 and (X or Y or Z):
        strip_hits["n"] += 1
    return orig_formal_t(P, p)
proto.formal_t = formal_t_instr

jac_only = 0
for (p, a, b) in [(43, 4, 2), (61, 0, 2)]:
    pts = [pt for pt in proto.all_affine(a, b, p) if pt[1] % p != 0]
    G = pts[0]
    for m in (1, 2, 3, 7, 11, p // 2):
        Q = proto.aff_mul(m, G, a, p)
        before = proto.OPS["point_add"]
        proto.smart_dlp(G, Q, a, b, p)
        jac_only += proto.OPS["point_add"] - before
print("(1) smart_dlp (Jacobian) ops over the 12 ANOM runs:", jac_only,
      "; total counter incl. affine setup:", proto.OPS["point_add"])
print("(2) stripping branch reached on tested path:", strip_hits["n"], "times")

# (3) weighted scaling vs uniform division
p = 43; M = p * p; a, b = 4, 2
pts = [pt for pt in proto.all_affine(a, b, p) if pt[1] % p != 0]
x, y = proto.hensel_y(pts[0][0], pts[0][1], a, b, p)
def on_curve_jac(X, Y, Z):
    return (Y * Y - (X ** 3 + a * X * Z ** 4 + b * Z ** 6)) % M == 0
lam = p
scaled = ((lam ** 2 * x) % M, (lam ** 3 * y) % M, lam % M)      # proper weighted scaling of (x,y,1)
uniform = (scaled[0] // p, scaled[1] // p, scaled[2] // p)      # what formal_t's loop does
print("(3) weighted-scaled triple on curve:", on_curve_jac(*scaled),
      "| uniformly divided by p on curve:", on_curve_jac(*uniform),
      "| formal_t(uniform) =", orig_formal_t(uniform, p))

# (4)+(5) E_1 point addition branch
p, a, b = 43, 4, 2; M = p * p
pts = [pt for pt in proto.all_affine(a, b, p) if pt[1] % p != 0]
G = pts[0]; Q = proto.aff_mul(7, G, a, p)
Gx, Gy = proto.hensel_y(G[0], G[1], a, b, p)
Qx, Qy = proto.hensel_y(Q[0], Q[1], a, b, p)
JP = proto.jac_mul(p, (Gx, Gy, 1), a, M)
JQ = proto.jac_mul(p, (Qx, Qy, 1), a, M)
tP, tQ = orig_formal_t(JP, p), orig_formal_t(JQ, p)
S = proto.jac_add(JP, JQ, a, M)
tS = orig_formal_t(S, p)
D = proto.jac_dbl(JP, a, M)
tD = orig_formal_t(D, p)
print("(4) tP=%d tQ=%d  jac_add(JP,JQ) -> t=%s ; expected tP+tQ mod p^2 = %d ; 2tP mod p^2 = %d"
      % (tP, tQ, tS, (tP + tQ) % M, (2 * tP) % M))
print("    JP,JQ Z-coords mod p:", JP[2] % p, JQ[2] % p, "(both E_1); U1==U2 and S1==S2 mod p^2 forced -> doubling branch taken:", tS == tD)
print("(5) t([2]JP) == 2 tP mod p^2:", tD == (2 * tP) % M, "; tQ == 7*tP mod p (log ratio):", (tQ // p) % p == (7 * (tP // p)) % p)

# (6) a-lift fix for (61,0,2), all six secrets
p, a, b = 61, 0, 2; M = p * p
pts = [pt for pt in proto.all_affine(a, b, p) if pt[1] % p != 0]
G = pts[0]
ok = 0
for m in (1, 2, 3, 7, 11, 30):
    Q = proto.aff_mul(m, G, a, p)
    # same hensel/jac code path, curve lift a' = 61 (== 0 mod 61), b = 2
    al = 61
    def hensel(x, y):
        y0 = y % p
        f = (pow(x, 3, M) + al * x + b) % M
        d = (f - y0 * y0) % M
        t = ((d // p) * proto.inv(2 * y0, p)) % p
        return x, (y0 + t * p) % M
    Gx, Gy = hensel(*G); Qx, Qy = hensel(*Q)
    JP = proto.jac_mul(p, (Gx, Gy, 1), al, M); JQ = proto.jac_mul(p, (Qx, Qy, 1), al, M)
    tP, tQ = orig_formal_t(JP, p), orig_formal_t(JQ, p)
    got = ((tQ // p) * proto.inv((tP // p) % p, p)) % p if tP and (tP // p) % p else None
    ok += (got == m)
print("(6) (61,0,2) with curve lift a=61,b=2: correct secrets", ok, "/ 6")
print("ops", proto.OPS, "sec", round(time.perf_counter() - T0, 3))
