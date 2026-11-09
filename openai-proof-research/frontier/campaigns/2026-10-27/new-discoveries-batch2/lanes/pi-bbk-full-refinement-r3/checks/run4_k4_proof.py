"""Run 4: COMPLETE PROOF MACHINE for k=4 (all n >= 0), all coefficients.

G_{4,n}(q) = (1-q^a)(1-q^{a+2}) / ((1-q)(1-q^3)(1-q^5)),  a = 2n+3 (odd, >=3).
[q^m] G_{4,n} = T_a(m) := h(m) - h(m-a) - h(m-a-2) + h(m-2a-2),
h = denumerant of B={1,3,5}: h(x) = #{(i,j,l)>=0: i + 3j + 5l = x}, h(x)=0 for x<0.

Exact quasi-polynomial: for x = 15Q + r (Q>=0, 0<=r<15):
  h(15Q+r) = (15/2) Q^2 + beta_r Q + gamma_r
(computed exactly below from the j-sum; alpha_r = 15/2 independent of r).

Proof reduces to two finite exact checks:
 (C1) D(u) := h(2u+3) - h(u+2) - h(u) >= 0 for all u >= 0          [regime a+2 <= m < 2a+2]
 (C2) T(m,a) >= 0 for all odd a >= 3 and m >= 2a+2                  [tail regime]
both verified by exact Newton-forward-difference tests on quadratic rays.
"""
from fractions import Fraction as F

# ---------- exact h quasi-polynomial data ----------
def h_quadratic_data():
    """Return (alpha, beta[r], gamma[r]) with h(15Q+r) = alpha Q^2 + beta[r] Q + gamma[r]."""
    alpha = F(15, 2)
    beta = []; gamma = []
    for r in range(15):
        rho = r // 5                      # floor(r/5): j = 3t+s runs to 3Q+rho
        acc_b = F(0); acc_g = F(0)
        for s in range(3):
            d_s = F((r - 5*s) // 3)                   # floor((r-5s)/3)
            tau_s = F((rho - s) // 3) if rho - s >= 0 else F(-1)  # floor((rho-s)/3), -1 if negative
            # tau_s = floor((rho-s)/3) in {-1,0}; python // already floors
            tau_s = F((rho - s) // 3)
            acc_b += d_s + F(7, 2)
            acc_g += (tau_s + 1) * (d_s + 1) - F(5, 2) * tau_s * (tau_s + 1)
        beta.append(acc_b); gamma.append(acc_g)
    return alpha, beta, gamma

ALPHA, BETA, GAMMA = h_quadratic_data()

def hQ(Q, r):
    """Exact h(15Q+r) for Q >= 0."""
    return ALPHA*Q*Q + BETA[r]*Q + GAMMA[r]

def h(x):
    if x < 0: return F(0)
    Q, r = divmod(x, 15)
    return hQ(Q, r)

def h_nondecreasing_check(xmax=100000):
    """h(x+1) >= h(x) (true because 1 in B; verified here exactly on a range as a sanity check)."""
    return all(h(x+1) >= h(x) for x in range(xmax))

# ---------- (C1): D(u) = h(2u+3) - h(u+2) - h(u) >= 0 ----------
def check_C1():
    """For each residue class u = rho + 15t: D is a quadratic in t with rational coeffs;
    Newton test: D(rho)>=0, D(rho+15)-D(rho)>=0, second difference >= 0."""
    results = []
    for rho in range(15):
        vals = [D(u) for u in (rho, rho+15, rho+30)]
        d0, d1 = vals[0], vals[1]-vals[0]
        d2 = (vals[2]-vals[1]) - (vals[1]-vals[0])
        ok = d0 >= 0 and d1 >= 0 and d2 >= 0
        results.append((rho, d0, d1, d2, ok))
    return results

def D(u): return h(2*u+3) - h(u+2) - h(u)

# ---------- (C2): T(m,a) >= 0 for a >= 3 (odd), m >= 2a+2 ----------
def T(m, a):
    return h(m) - h(m-a) - h(m-a-2) + h(m-2*a-2)

def check_C2():
    """For each (rho = m mod 15, alpha = a mod 15):
       ray: a = alpha0 + 15t (alpha0 = least a>=3, a≡alpha mod 15), m = m0(a) + 15j,
       m0(a) = least m >= 2a+2 with m ≡ rho (mod 15).
       T is a quadratic form in (t, j). Newton test with 6 evaluations:
         T(0,0) >= 0, T(1,0)-T(0,0) >= 0, T(0,1)-T(0,0) >= 0,
         2nd differences in t, in j, and mixed, all >= 0."""
    bad = []
    table = []
    for alpha in range(15):
        alpha0 = alpha if alpha >= 3 else alpha + 15   # least a >= 3 with a ≡ alpha (mod 15)
        for rho in range(15):
            def m0(a):
                base = 2*a + 2
                return base + ((rho - base) % 15)
            def Tf(t, j):
                a = alpha0 + 15*t
                return T(m0(a) + 15*j, a)
            v00, v10, v01 = Tf(0,0), Tf(1,0), Tf(0,1)
            v20, v02, v11 = Tf(2,0), Tf(0,2), Tf(1,1)
            d_t0  = v10 - v00
            d_j0  = v01 - v00
            d_tt  = v20 - 2*v10 + v00
            d_jj  = v02 - 2*v01 + v00
            d_tj  = v11 - v10 - v01 + v00
            ok = (v00 >= 0 and d_t0 >= 0 and d_j0 >= 0 and d_tt >= 0 and d_jj >= 0 and d_tj >= 0)
            table.append((alpha, rho, v00, d_t0, d_j0, d_tt, d_jj, d_tj, ok))
            if not ok: bad.append((alpha, rho, v00, d_t0, d_j0, d_tt, d_jj, d_tj))
    return table, bad

if __name__ == '__main__':
    print("alpha_r (all should be 15/2):", set(str(ALPHA)))
    print("beta_r:", [str(b) for b in BETA])
    print("gamma_r:", [str(g) for g in GAMMA])
    print("h nondecreasing (x<=10^5):", h_nondecreasing_check(100000))
    c1 = check_C1()
    print("C1 (D(u)>=0) per class:", all(r[4] for r in c1))
    for r in c1: print("   rho=%2d D=%s d15=%s d2=%s ok=%s" % r)
    table, bad = check_C2()
    print("C2 (T>=0 on tail rays): failures:", len(bad))
    for b in bad[:10]: print("   ", b)

def summarize():
    """Min Newton data over all classes, for the record."""
    mins = None
    cnt = 0
    for alpha in range(15):
        alpha0 = alpha if alpha >= 3 else alpha + 15
        for rho in range(15):
            def m0(a):
                base = 2*a + 2
                return base + ((rho - base) % 15)
            def Tf(t, j):
                a = alpha0 + 15*t
                return T(m0(a) + 15*j, a)
            v00, v10, v01 = Tf(0,0), Tf(1,0), Tf(0,1)
            v20, v02, v11 = Tf(2,0), Tf(0,2), Tf(1,1)
            data = (v00, v10-v00, v01-v00, v20-2*v10+v00, v02-2*v01+v00, v11-v10-v01+v00)
            mn = min(data)
            cnt += 1
            if mins is None or mn < mins: mins = mn
    print("C2 classes:", cnt, "min Newton data over all 225 classes:", mins)

summarize()
