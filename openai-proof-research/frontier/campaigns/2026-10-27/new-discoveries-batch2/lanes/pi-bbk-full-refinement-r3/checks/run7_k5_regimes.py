"""Run 7: k=5 proof machine v2 — regime-exact certificates.

Regimes for T(m,a) = [q^m] G_{5,n}, a = 2n+3 >= 3:
  R1 [a, a+2)      : T = h(m) - h(m-a)                    >= 0 by monotonicity of h.
  R2 [a+2, a+4)    : T = h(a+2+u) - h(u+2) - h(u), u=0,1  >= D(u) >= 0 (k=4 lemma C1).
  R3 [a+4, 2a+2)   : wedge  u = m-(a+4) in [0, a-3]
  R4 [2a+2, 2a+4)  : width-2 slab (m = 2a+2+delta, delta in {0,1})
  R5 [2a+4, 2a+6)  : width-2 slab
  R6 [2a+6, 3a+6)  : wedge  u = m-(2a+6) in [0, a-1]
  R7 [3a+6, inf)   : quadrant (PASSED in run6)

Certificates:
  width-2 slabs: per (alpha,rho) class T is an exact cubic in t (a = alpha0+105t);
                 univariate Newton data (4 values, t=0..3) all >= 0.
  wedges: per class, u = u0 + 105w; constraint w <= t + c (c in {-1,0});
          cover wedge = {w <= c} strip (finite rays in t)  U  {w >= max(c+1,0), t = w-c+s, s>=0}
          (a quadrant in (w,s) -> 10-point staircase test).
All evaluations exact (Fraction) via the verified cubic quasi-polynomial of h.
"""
import sys
from fractions import Fraction as F
sys.path.insert(0, '.')
from gkn_core import series_inv, q_pochhammer_odd

N = 5000
H = series_inv(q_pochhammer_odd(1, 4), N)
def hser(x): return H[x] if 0 <= x < len(H) else None
L = 105

def fit_cubic(vals):
    v0, v1, v2, v3 = (F(v) for v in vals)
    return (v0, v1-v0, v2-2*v1+v0, v3-3*v2+3*v1-v0)
def hpoly(Q, d):
    v0, d1, d2, d3 = d
    return v0 + Q*d1 + F(Q*(Q-1), 2)*d2 + F(Q*(Q-1)*(Q-2), 6)*d3
CUBIC = [fit_cubic([hser(105*Q+r) for Q in range(4)]) for r in range(L)]
assert all(hpoly(Q, CUBIC[r]) == F(hser(105*Q+r)) for r in range(L) for Q in range(4, 10))
def hQ(x):
    if x < 0: return F(0)
    Q, r = divmod(x, L)
    return hpoly(Q, CUBIC[r])

def T5(m, a):
    s = hQ(m) if m >= 0 else F(0)
    for c in (a, a+2, a+4):
        if m-c >= 0: s -= hQ(m-c)
    for c in (2*a+2, 2*a+4, 2*a+6):
        if m-c >= 0: s += hQ(m-c)
    if m-3*a-6 >= 0: s -= hQ(m-3*a-6)
    return s

# regime formulas (active sets); each returns the exact coefficient on the regime
def T_R3(m, a): return hQ(m) - hQ(m-a) - hQ(m-a-2) - hQ(m-a-4)
def T_R4(m, a): return T_R3(m,a) + hQ(m-2*a-2)
def T_R5(m, a): return T_R4(m,a) + hQ(m-2*a-4)
def T_R6(m, a): return T_R5(m,a) + hQ(m-2*a-6)
def T_R7(m, a): return T_R6(m,a) - hQ(m-3*a-6)

# ---- cross-check regime formulas vs T5 on the regimes ----
def crosscheck():
    bad = []
    for a in [3,4,5,8,50,105,106,200,316,500]:
        for name, lo, hi, f in [("R3", a+4, 2*a+2, T_R3), ("R4", 2*a+2, 2*a+4, T_R4),
                                ("R5", 2*a+4, 2*a+6, T_R5), ("R6", 2*a+6, 3*a+6, T_R6),
                                ("R7", 3*a+6, 3*a+6+400, T_R7)]:
            for m in list(range(lo, min(hi, lo+40))) + ([hi-1] if hi-1 >= lo else []):
                if T5(m, a) != f(m, a): bad.append((name, a, m))
    return bad

# ---- width-2 slab certificate ----
def slab_test(T_f, base):   # base(a) = 2a+2 or 2a+4 ; m = base(a)+delta
    bad = []
    for alpha in range(L):
        alpha0 = alpha if alpha >= 3 else alpha + L
        for rho in range(L):
            d = (rho - 2*alpha - (2 if T_f is T_R4 else 4)) % L
            if d >= 2: continue    # no m in this class falls in the slab
            vals = [T_f(base(alpha0 + L*t) + d, alpha0 + L*t) for t in range(4)]
            d1 = vals[1]-vals[0]; d2 = vals[2]-2*vals[1]+vals[0]; d3 = vals[3]-3*vals[2]+3*vals[1]-vals[0]
            if vals[0] < 0 or d1 < 0 or d2 < 0 or d3 < 0:
                bad.append((alpha, rho, d, [str(v) for v in (vals[0], d1, d2, d3)]))
    return bad

# ---- wedge certificate ----
def wedge_test(T_f, u_shift, slack):
    """regime m = boundary(a) + u, u in [0, a - slack];  boundary = c_a*a + u_shift.
       T_R3: boundary = a+4   (u_shift=4, coeff 1), slack: u <= a-3
       T_R6: boundary = 2a+6  (u_shift=6, coeff 2), slack: u <= a-1"""
    coeff = 1 if T_f is T_R3 else 2
    ushift = u_shift
    bad = []
    for alpha in range(L):
        alpha0 = alpha if alpha >= 3 else alpha + L
        for rho in range(L):
            u0 = (rho - coeff*alpha - ushift) % L
            # constraint: u <= a - slack  <=>  105w <= 105t + alpha0 - slack - u0
            C = alpha0 - slack - u0
            c = C // L           # in {-1, 0} given ranges
            def Tf(t, w): return T_f(coeff*(alpha0+L*t) + ushift + u0 + L*w, alpha0 + L*t)
            # strip: 0 <= w <= c (only if c >= 0); rays in t for each w
            strip_ok = True
            for w in range(0, max(c, -1)+1):
                if w > c: break
                tmin = max(0, w - c)
                vals = [Tf(tmin + tau, w) for tau in range(4)]
                d1 = vals[1]-vals[0]; d2 = vals[2]-2*vals[1]+vals[0]; d3 = vals[3]-3*vals[2]+3*vals[1]-vals[0]
                if vals[0] < 0 or d1 < 0 or d2 < 0 or d3 < 0:
                    strip_ok = False; bad.append(("strip", alpha, rho, w, [str(v) for v in (vals[0],d1,d2,d3)]))
            # quadrant region: w >= max(c+1, 0), t = w - c + s, s >= 0  -> cubic form in (w,s)
            w0 = max(c+1, 0)
            def Tf2(w, s): return Tf(w - c + s, w)
            pts = {(0,0): Tf2(w0,0), (1,0): Tf2(w0+1,0), (0,1): Tf2(w0,1),
                   (2,0): Tf2(w0+2,0), (1,1): Tf2(w0+1,1), (0,2): Tf2(w0,2),
                   (3,0): Tf2(w0+3,0), (2,1): Tf2(w0+2,1), (1,2): Tf2(w0+1,2), (0,3): Tf2(w0,3)}
            p00 = pts[(0,0)]
            data = [p00,
                    pts[(1,0)]-p00, pts[(0,1)]-p00,
                    pts[(2,0)]-2*pts[(1,0)]+p00,
                    pts[(1,1)]-pts[(1,0)]-pts[(0,1)]+p00,
                    pts[(0,2)]-2*pts[(0,1)]+p00,
                    pts[(3,0)]-3*pts[(2,0)]+3*pts[(1,0)]-p00,
                    pts[(2,1)]-pts[(2,0)]-2*pts[(1,1)]+2*pts[(1,0)]+pts[(0,1)]-p00,
                    pts[(1,2)]-2*pts[(1,1)]-pts[(0,2)]+2*pts[(0,1)]+pts[(1,0)]-p00,
                    pts[(0,3)]-3*pts[(0,2)]+3*pts[(0,1)]-p00]
            if any(dv < 0 for dv in data):
                bad.append(("quad", alpha, rho, [str(dv) for dv in data]))
    return bad

if __name__ == '__main__':
    bad = crosscheck()
    print("regime-formula crosscheck failures:", len(bad), bad[:5])

    b4 = slab_test(T_R4, lambda a: 2*a+2)
    print("R4 slab failures:", len(b4), b4[:3])
    b5 = slab_test(T_R5, lambda a: 2*a+4)
    print("R5 slab failures:", len(b5), b5[:3])
    b3 = wedge_test(T_R3, 4, 3)
    print("R3 wedge failures:", len(b3), b3[:3])
    b6 = wedge_test(T_R6, 6, 1)
    print("R6 wedge failures:", len(b6), b6[:3])
    print("DONE")
