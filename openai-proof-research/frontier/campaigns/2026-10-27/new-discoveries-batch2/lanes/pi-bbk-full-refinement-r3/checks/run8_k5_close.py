"""Run 8: close the k=5 proof gaps.
 (a) R2 slab certificate (T = h(m)-h(m-a)-h(m-a-2) on m in [a+2, a+4), u = m-a-2 in {0,1}).
 (b) R1 slab certificate for completeness (T = h(m)-h(m-a) on m in [a, a+2)).
 (c) LOOP CLOSURE: [q^m] of the direct series of G_{5,n} == T5(m,a) (hQ-based) on a grid.
"""
import sys
from fractions import Fraction as F
sys.path.insert(0, '.')
from gkn_core import series_inv, q_pochhammer_odd, series_mul

N = 5000
H = series_inv(q_pochhammer_odd(1, 4), N)
L = 105
def fit_cubic(vals):
    v0, v1, v2, v3 = (F(v) for v in vals)
    return (v0, v1-v0, v2-2*v1+v0, v3-3*v2+3*v1-v0)
def hpoly(Q, d):
    v0, d1, d2, d3 = d
    return v0 + Q*d1 + F(Q*(Q-1), 2)*d2 + F(Q*(Q-1)*(Q-2), 6)*d3
CUBIC = [fit_cubic([F(H[105*Q+r]) for Q in range(4)]) for r in range(L)]
def hQ(x):
    if x < 0: return F(0)
    Q, r = divmod(x, L)
    return hpoly(Q, CUBIC[r])

def slab2(T_args):  # T_args(m,a) with 2- or 3-term active sets; m = base(a)+delta
    bad = []
    for alpha in range(L):
        alpha0 = alpha if alpha >= 3 else alpha + L
        for rho in range(L):
            d = (rho - 2*alpha - T_args['off']) % L
            if d >= T_args['width']: continue
            vals = [T_args['f'](T_args['base'](alpha0+L*t)+d, alpha0+L*t) for t in range(4)]
            d1 = vals[1]-vals[0]; d2 = vals[2]-2*vals[1]+vals[0]; d3 = vals[3]-3*vals[2]+3*vals[1]-vals[0]
            if vals[0] < 0 or d1 < 0 or d2 < 0 or d3 < 0:
                bad.append((alpha, rho, d, [str(v) for v in (vals[0],d1,d2,d3)]))
    return bad

R1 = dict(off=0, width=2, base=lambda a: a,     f=lambda m,a: hQ(m)-hQ(m-a))
R2 = dict(off=2, width=2, base=lambda a: a+2,   f=lambda m,a: hQ(m)-hQ(m-a)-hQ(m-a-2))

# (c) loop closure: direct series vs T5
def T5(m, a):
    s = hQ(m) if m >= 0 else F(0)
    for c in (a, a+2, a+4):
        if m-c >= 0: s -= hQ(m-c)
    for c in (2*a+2, 2*a+4, 2*a+6):
        if m-c >= 0: s += hQ(m-c)
    if m-3*a-6 >= 0: s -= hQ(m-3*a-6)
    return s

def loop_closure():
    bad = 0; checked = 0
    for n in [0,1,2,3,5,8,13,21,40]:
        a = 2*n+3
        g = series_mul(q_pochhammer_odd(a,3), series_inv(q_pochhammer_odd(1,4), 3000))[:3001]
        for m in range(0, 3001):
            if g[m] != T5(m, a): bad += 1
            checked += 1
    return bad, checked

if __name__ == '__main__':
    b1 = slab2(R1); b2 = slab2(R2)
    print("R1 slab failures:", len(b1), b1[:2])
    print("R2 slab failures:", len(b2), b2[:2])
    bad, checked = loop_closure()
    print(f"loop closure (direct series == T5): {bad} mismatches out of {checked}")
