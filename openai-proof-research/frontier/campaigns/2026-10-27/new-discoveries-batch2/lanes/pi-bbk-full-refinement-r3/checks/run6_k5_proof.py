"""Run 6: k=5 proof machine — G_{5,n} >= 0 for ALL n, via exact cubic quasi-polynomials.

G_{5,n}(q) = (1-q^a)(1-q^{a+2})(1-q^{a+4}) / ((1-q)(1-q^3)(1-q^5)(1-q^7)), a = 2n+3.
[q^m] = sum_{S subset A} (-1)^{|S|} h(m - sigma(S)),  h = denumerant{1,3,5,7}, h(x)=0 x<0.

h(105Q+r) is an EXACT cubic in Q per r (period lcm(1,3,5,7)=105, degree 3):
fitted exactly from the series, then verified against the series for Q=4..9.

Regimes (half-open), with the active subsets listed; on each regime all active
arguments are >= 0, so T is an exact cubic form in the class parameters (t, j):
  a = alpha0 + 105 t,  m = boundary(a) + delta + 105 j.
Test: all 10 staircase Newton data Δ^{i,k}T(0,0), i+k<=3, >= 0  ==> T >= 0 on the
quadrant (t,j>=0), hence on the regime triangle (j bounded above by the regime).
"""
import sys
from fractions import Fraction as F
sys.path.insert(0, '.')
from gkn_core import series_inv, q_pochhammer_odd

N = 5000
H = series_inv(q_pochhammer_odd(1, 4), N)   # 1/((1-q)(1-q^3)(1-q^5)(1-q^7))
def h(x): return H[x] if 0 <= x <= N else None

L = 105
# ---- exact cubic fit of h(105Q+r) ----
# Solve Vandermonde for Q=0..3 per r: c0 + c1 Q + c2 Q^2 + c3 Q^3 = h(105Q+r)
def fit_cubic(vals):  # vals[Q] for Q=0..3
    # Lagrange basis in Q
    c = []
    # coefficients of Q^k via solving 3x3... do direct: p(Q)=c0+c1Q+c2Q^2+c3Q^3
    # Use finite differences: p(Q) = v0 + Q Δv0 + C(Q,2) Δ²v0 + C(Q,3) Δ³v0 for cubic fit? Only exact if vals are cubic samples — they are (h is cubic in Q). Use Newton forward form.
    v0, v1, v2, v3 = vals
    d1 = v1 - v0; d2 = v2 - 2*v1 + v0; d3 = v3 - 3*v2 + 3*v1 - v0
    return (v0, d1, d2, d3)   # p(Q) = v0 + Q d1 + C(Q,2) d2 + C(Q,3) d3

def hpoly(Q, data):
    v0, d1, d2, d3 = data
    return v0 + Q*d1 + F(Q*(Q-1), 2)*d2 + F(Q*(Q-1)*(Q-2), 6)*d3

CUBIC = []
for r in range(L):
    vals = [F(h(105*Q + r)) for Q in range(4)]
    CUBIC.append(fit_cubic(vals))
# verify against series
ok = True
for r in range(L):
    for Q in range(4, 10):
        if hpoly(Q, CUBIC[r]) != F(h(105*Q + r)):
            ok = False; print("cubic mismatch", r, Q)
print("cubic quasi-poly verified vs series (Q<=9, all r):", ok)

def hQ(x):
    if x < 0: return F(0)
    Q, r = divmod(x, L)
    return hpoly(Q, CUBIC[r])

def T5_terms(m, a, active):
    """sum (-1)^{|S|} h(m - sigma(S)) over active subset-size pattern."""
    s = F(0)
    if 's' in active:
        for c in (a, a+2, a+4): s -= hQ(m - c)
    if 'p2' in active: s += hQ(m - 2*a - 2)
    if 'p4' in active: s += hQ(m - 2*a - 4)
    if 'p6' in active: s += hQ(m - 2*a - 6)
    if 't' in active:  s -= hQ(m - 3*a - 6)
    return s + hQ(m)

# regime definitions: (name, boundary(a), active set)
REGIMES = [
    ("R1 [a,a+2)",        lambda a: a,        set()),
    ("R2 [a+2,a+4)",      lambda a: a+2,      set()),
    ("R3 [a+4,2a+2)",     lambda a: a+4,      set()),
    ("R4 [2a+2,2a+4)",    lambda a: 2*a+2,    {'p2'}),
    ("R5 [2a+4,2a+6)",    lambda a: 2*a+4,    {'p2','p4'}),
    ("R6 [2a+6,3a+6)",    lambda a: 2*a+6,    {'p2','p4','p6'}),
    ("R7 [3a+6,inf)",     lambda a: 3*a+6,    {'p2','p4','p6','t'}),
]

def T5(m, a):
    """true coefficient: all subsets, h(x)=0 for x<0."""
    s = F(h(m)) if m >= 0 else F(0)
    for c in (a, a+2, a+4): s -= hQ(m-c) if m-c >= 0 else 0
    for c in (2*a+2, 2*a+4, 2*a+6): s += hQ(m-c) if m-c >= 0 else 0
    s -= hQ(m-3*a-6) if m-3*a-6 >= 0 else 0
    return s

def staircase_test(reg_name, boundary, active):
    """For each (rho mod 105, alpha mod 105): T(t,j) cubic form; check 10 Newton data >= 0."""
    bad = []
    for alpha in range(L):
        alpha0 = alpha if alpha >= 3 else alpha + L
        for rho in range(L):
            def m0(t):
                a = alpha0 + L*t
                b = boundary(a)
                return b + ((rho - b) % L)
            def Tf(t, j): return T5(m0(t) + L*j, alpha0 + L*t)
            # 10 staircase points
            pts = {(0,0): Tf(0,0), (1,0): Tf(1,0), (0,1): Tf(0,1),
                   (2,0): Tf(2,0), (1,1): Tf(1,1), (0,2): Tf(0,2),
                   (3,0): Tf(3,0), (2,1): Tf(2,1), (1,2): Tf(1,2), (0,3): Tf(0,3)}
            d00 = pts[(0,0)]
            d10 = pts[(1,0)] - d00
            d01 = pts[(0,1)] - d00
            d20 = pts[(2,0)] - 2*pts[(1,0)] + d00
            d11 = pts[(1,1)] - pts[(1,0)] - pts[(0,1)] + d00
            d02 = pts[(0,2)] - 2*pts[(0,1)] + d00
            d30 = pts[(3,0)] - 3*pts[(2,0)] + 3*pts[(1,0)] - d00
            d21 = pts[(2,1)] - pts[(2,0)] - 2*pts[(1,1)] + 2*pts[(1,0)] + pts[(0,1)] - d00
            d12 = pts[(1,2)] - 2*pts[(1,1)] - pts[(0,2)] + 2*pts[(0,1)] + pts[(1,0)] - d00
            d03 = pts[(0,3)] - 3*pts[(0,2)] + 3*pts[(0,1)] - d00
            data = [d00, d10, d01, d20, d11, d02, d30, d21, d12, d03]
            if any(dv < 0 for dv in data):
                bad.append((alpha, rho, [str(dv) for dv in data]))
    return bad

if __name__ == '__main__':
    total_bad = 0
    for name, boundary, active in REGIMES:
        bad = staircase_test(name, boundary, active)
        print(f"{name}: failing classes = {len(bad)}")
        for b in bad[:3]: print("    ", b)
        total_bad += len(bad)
    print("TOTAL failing classes:", total_bad)
