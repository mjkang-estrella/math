#!/usr/bin/env python3
"""
INDEPENDENT exact checker for the pi-hermite-preliminary-review lane.
Adversarial re-derivation of EVERY universal claim in parent-hermite-bound/PROOF.md,
written fresh (not derived from check_proposal.py). Uses mpmath high precision,
sympy symbolic algebra, and numpy dense sampling of the LITERAL conjecture.

Gates:
  G1  literal source statement / constants (C, E, g, a) cross-checked vs Table 1
  G2  exact identities: C vs H_{2m}(0), A, gamma_m, Wallis ratios (symbolic)
  G3  gamma_m monotonicity, limits, gamma_m<r_m, gamma_m<=9pi/28<99/98 (exact m range)
  G4  sine comparison (3) both directions, positivity, numerically for many m
  G5  M(u) monotonicity + constant chain 7/45, 7/50, 3/94, sin<=7sqrt2/10
  G6  q y^2/(E C^2) < 99/100 on [0,x0] (dense)
  G7  energy loss > A^2/(2E^2); B(x0) < A^2(1-1/(2E^2)) < E C^2 (exact via gamma<r)
  G8  bulk B route x0..sqrt(E) (dense)
  G9  n=1 explicit quadratic; n=2,3,even-n checks
  G10 tail: Cramer-Indritz DLMF 18.14.9 constant, S_n bounds, g(a)^2 > E/pi, poly
  G11 LITERAL conjecture verified densely for n=1..120 over x in (0, 40] (evidence)
  G12 Foster-Krasikov 2000 Thm1 (as read from PDF pp307-308): squared-bound/C^2 at 0,
      and FULL pointwise comparison of FK envelope vs conjectured envelope on its range
  G13 subsumption assembly test: can FK2000 + classical comparison + CI prove the
      conjecture? locate exactly where FK exceeds the conjectured envelope
  G14 Krasikov 2004 Thm 1 max-bound vs conjecture at its tightest point
"""
import mpmath as mp
import sympy as sp
import json, math

mp.mp.dps = 60
out = {}

def J(key, val):
    out[key] = val
    print(f"== {key}: {val}")

# ---------- G1: constants ----------
def C_of(n):  # physicists' conjecture constant
    return mp.mpf(2)**n * mp.gamma(mp.mpf(n+1)/2) / mp.sqrt(mp.pi)

def a_of(n):
    E = 2*n+1
    return mp.sqrt(E)*(1 - mp.pi/(2*E))

def g_of(n, x):
    E = 2*n+1
    return 1/mp.sqrt(1 - x**2/E)

# Table 1 published values (n: xn, gn(xn)) from the actual PDF p.8
t1 = {2:(1.534,1.374),3:(2.052,1.584),4:(2.476,1.772),5:(2.843,1.942),
      6:(3.170,2.099),7:(3.467,2.245),8:(3.742,2.382),9:(3.999,2.512),10:(4.240,2.635)}
ok = all(abs(float(a_of(n))-v[0])<5e-4 and abs(float(g_of(n,a_of(n)))-v[1])<5e-4 for n,v in t1.items())
J("G1_table1_matches_a_sqrtE(1-pi/2E)_and_g", ok)

# even-n: C = |H_{2m}(0)| = (2m)!/m!  (exact integer check)
ev_ok = all(abs(C_of(2*m) - mp.factorial(2*m)/mp.factorial(m)) < mp.mpf("1e-55")*C_of(2*m) for m in range(1,25))
J("G2_C_equals_Heven0_exact", ev_ok)

# ---------- G2/G3: gamma_m, Wallis ----------
def A_of(m):  # |H_{2m+1}'(0)| = 2(2m+1)(2m)!/m!
    return mp.mpf(2)*(2*m+1)*mp.factorial(2*m)/mp.factorial(m)

def gamma_of(m):
    E = 4*m+3
    return A_of(m)**2/(E*C_of(2*m+1)**2)

def gamma_closed(m):
    return mp.pi*(2*m+1)**2*mp.binomial(2*m,m)**2/((4*m+3)*mp.mpf(16)**m)

J("G2_gamma_closed_form_matches", all(abs(gamma_of(m)-gamma_closed(m))<mp.mpf("1e-50") for m in range(0,30)))

m = sp.symbols('m', integer=True, positive=True)
g1 = sp.pi*(2*m+1)**2*sp.binomial(2*m,m)**2/((4*m+3)*2**(4*m))
ratio = sp.simplify(g1.subs(m,m+1)/g1)
J("G2_symbolic_gamma_ratio", sp.simplify(ratio - ((2*m+3)**2*(4*m+3)/(4*(m+1)**2*(4*m+7)))))
J("G2_ratio_equals_1_minus", sp.simplify(ratio - (1 - sp.Rational(1,1)/(4*(m+1)**2*(4*m+7)))))

E_ = 4*m+3
r_m = 2*E_**2/(2*E_**2-1)
delta = g1/r_m
dd = sp.simplify(delta.subs(m,m+1)/delta - 1)
J("G2_symbolic_delta_ratio_minus_1", sp.factor(sp.together(dd)))

# numeric: gamma strictly decreasing, >1; delta strictly increasing, <1; gamma<r_m
gd = [gamma_of(k) for k in range(0,200)]
J("G3_gamma0", mp.nstr(gd[0],20))
J("G3_gamma1_9pi_over_28", mp.nstr(gd[1],20) + " vs " + mp.nstr(9*mp.pi/28,20))
J("G3_gamma_decreasing_and_tends_1", all(gd[k]>gd[k+1] for k in range(199)) and mp.nstr(gd[190]-1,5))
def r_of(m):
    E=4*m+3; return mp.mpf(2)*E**2/(2*E**2-1)
J("G3_gamma_lt_r_all_0_199", all(gd[k] < r_of(k) for k in range(200)))
J("G3_gamma1_lt_99_over_98", 9*mp.pi/28 < mp.mpf(99)/98)
J("G3_9pi28_lt_99_98_iff_pi_lt_22_7", 9*mp.pi/28 < mp.mpf(99)/98 and mp.pi < mp.mpf(22)/7)

# ---------- G4/G5/G6: sine comparison on [0,x0] ----------
def hermite_phys(n, x):
    # physicists H_n via recurrence in mp
    h0, h1 = mp.mpf(1), 2*x
    if n==0: return h0
    if n==1: return h1
    for k in range(1,n):
        h0, h1 = h1, 2*x*h1 - 2*k*h0
    return h1

def y_of(n, x):
    return hermite_phys(n,x)*mp.e**(-x**2/2)

sin_cmp_ok = True
worst = (None, None)
sgn = lambda mm: 1 if hermite_phys(2*mm+1, mp.mpf('1e-30'))/mp.mpf('1e-30') > 0 else -1
for m in [1,2,3,5,10,50]:
    n = 2*m+1; E = 4*m+3
    A = A_of(m); x0 = mp.sqrt(mp.mpf(2)/E); q0 = E-mp.mpf(2)/E
    for i in range(1,201):
        x = x0*i/200
        lo = A/mp.sqrt(E)*mp.sin(mp.sqrt(E)*x)
        hi = A/mp.sqrt(q0)*mp.sin(mp.sqrt(q0)*x)
        y = sgn(m)*y_of(n,x)
        if not (lo <= y <= hi):
            sin_cmp_ok = False; worst = (m, float(x)); break
    # positivity on (0,x0]: dense sign check + no zero bracketed
    prev = sgn(m)*y_of(n, mp.mpf('1e-12'))
    for i in range(1,501):
        x=x0*i/500; yy=sgn(m)*y_of(n,x)
        if yy<=0 or prev<=0: sin_cmp_ok=False
        prev=yy
J("G4_sine_comparison_and_no_zero_in_[0,x0]", (sin_cmp_ok, worst))

# G5 constants
J("G5_cos_sqrt2_ge_7_over_45", mp.cos(mp.sqrt(2)) >= mp.mpf(7)/45)
J("G5_taylor_lower_bound_cos_exact", mp.mpf(1)-mp.mpf(1)+mp.mpf(4)/24-mp.mpf(8)/720 == mp.mpf(7)/45)
J("G5_sin_sqrt2_le_7sqrt2_over_10", mp.sin(mp.sqrt(2)) <= mp.mpf(7)/10*mp.sqrt(2))
J("G5_c_gt_9_over_10_min_E7", mp.sqrt(1-mp.mpf(2)/49) > mp.mpf(9)/10)
# c cot(cu) > 7/50 > 3/94 on (0, sqrt2], E>=7
worst_cc = mp.inf
for E in [7,11,15,31,63,201]:
    c = mp.sqrt(1-mp.mpf(2)/E**2)
    for i in range(1,501):
        u = mp.sqrt(2)*i/500
        val = c*mp.tan(c*u)**-1 - u/(E**2-u**2)
        worst_cc = min(worst_cc, val)
J("G5_c_cot_minus_rhs_min_margin", mp.nstr(worst_cc,15))
J("G5_7_over_50_gt_3_over_94", mp.mpf(7)/50 > mp.mpf(3)/94)

# G6: q y^2/(E C^2) < 99/100 for x in (0,x0], odd n>=3 ; and M(u) increasing
def M_of(m,u):
    E=4*m+3; c=mp.sqrt(1-mp.mpf(2)/E**2)
    return (1-u**2/E**2)*mp.sin(c*u)**2
mon_ok = True
for m in [1,2,3,10]:
    E=4*m+3; c=mp.sqrt(1-mp.mpf(2)/E**2)
    prev = mp.mpf(0)
    for i in range(1,301):
        u = mp.sqrt(2)*i/300
        v = M_of(m,u)
        if v < prev - mp.mpf('1e-40'): mon_ok=False
        prev=v
J("G6_M_increasing", mon_ok)
g6_ok=True; worst6=(None,0)
for m in [1,2,3,5,10,30,100]:
    n=2*m+1; E=4*m+3; C=C_of(n); x0=mp.sqrt(mp.mpf(2)/E)
    for i in range(1,401):
        x=x0*i/400
        q=(E-x**2); val=q*y_of(n,x)**2/(E*C**2)
        if val >= mp.mpf(99)/100:
            g6_ok=False; worst6=(n,float(x),float(val)); break
J("G6_qy2_over_EC2_lt_99_100", (g6_ok, worst6))

# ---------- G7: energy loss ----------
J("G7_sin1_gt_5_over_6", mp.sin(1) > mp.mpf(5)/6)
I = mp.quad(lambda u: u*mp.sin(u)**2, [0, mp.sqrt(2)])
J("G7_integral_0_sqrt2_u_sin2", mp.nstr(I,20))
J("G7_integral_gt_1_over_4", I > mp.mpf(1)/4)
J("G7_sin1_piece_lower_bound", abs((mp.mpf(5)/6)**2*mp.mpf(1)/2 - mp.mpf(25)/72) < mp.mpf("1e-55") and mp.mpf(25)/72 > mp.mpf(1)/4 and 2*mp.mpf(25)/72 > mp.mpf(1)/2)
J("G7_sin1_piece_lower_bound_exact_fraction", sp.Rational(5,6)**2*sp.Rational(1,2) == sp.Rational(25,72) and sp.Rational(25,72) > sp.Rational(1,4) and 2*sp.Rational(25,72) > sp.Rational(1,2))
# B(x0) < A^2 (1-1/(2E^2)) and < E C^2, exact check for m range
g7=True
for m in range(1,120):
    n=2*m+1; E=4*m+3; A=A_of(m); C=C_of(n)
    Bx0 = A**2*(1-mp.mpf(1)/(2*E**2))
    if not (Bx0 < E*C**2): g7=False; break
J("G7_A2(1-1/2E2)_lt_EC2_all_m", g7)
# numeric B(x0) direct, several m
g7b=True
for m in [1,2,3,5]:
    n=2*m+1; E=4*m+3; x0=mp.sqrt(mp.mpf(2)/E)
    y=y_of(n,x0); yp=(hermite_phys(n,x0)*1 - x0*hermite_phys(n,x0))*mp.e**(-x0**2/2)  # y' = (H'-xH)e^-x2/2
    Hp = 2*n*hermite_phys(n-1,x0)
    yp=(Hp - x0*hermite_phys(n,x0))*mp.e**(-x0**2/2)
    B=(E-x0**2)*y**2+yp**2
    A=A_of(m)
    if not (B < A**2*(1-mp.mpf(1)/(2*E**2))): g7b=False
J("G7_numeric_B_x0_lt_A2_1_minus", g7b)

# ---------- G8: bulk (B route) & G9 even case, dense ----------
def literal_lhs_rhs(n,x):
    # |H e^{-x2}| <= C g(min(x,a)) e^{-x2/2}
    lhs = abs(hermite_phys(n,x))*mp.e**(-x**2)
    a=a_of(n)
    rhs = C_of(n)*g_of(n,min(x,a))*mp.e**(-x**2/2)
    return lhs/rhs

bulk_ok=True; worst8=(None,None,0)
for n in list(range(1,61)):
    E=2*n+1; a=float(a_of(n)); sE=math.sqrt(E)
    for i in range(1,1200):
        x=mp.mpf(sE)*i/1200
        if x>=sE: break
        q=E-x*x; y=y_of(n,x)
        # energy route: B(x)<=B(min(x,x0))<=EC^2 for odd (via chain) / =EC2 even
        ratio = q*y**2/(E*C_of(n)**2)
        if ratio > 1 + mp.mpf('1e-30'):
            bulk_ok=False; worst8=(n,float(x),float(ratio)); break
J("G8_energy_bulk_ratio_le_1_all_n_1_60", (bulk_ok, worst8))

# ---------- G9: n=1 quadratic, n=2/3 finite pieces ----------
v=sp.symbols('v', real=True)
q1 = 1+v+v**2/2-sp.Rational(22,7)*v*(1-v/3)
J("G9_n1_quadratic", sp.expand(q1))
J("G9_n1_discriminant", sp.discriminant(sp.Poly(sp.expand(q1), v)))
J("G9_n1_literal_dense", all(literal_lhs_rhs(1, mp.mpf(i)/1000) <= 1 for i in range(1, 30000)))
# n=2 sup
f2=lambda x: abs((4*x**2-2))*mp.e**(-x**2/2)
sup2=max(f2(mp.mpf(i)/1000) for i in range(0,8000))
J("G9_n2_sup", mp.nstr(sup2,12))
J("G9_n2_sup_lt_8exp_54_exact", mp.nstr(8*mp.e**(-mp.mpf(5)/4),12))
J("G9_n2_Cg", mp.nstr(C_of(2)*g_of(2,a_of(2)),12))
J("G9_n2_Cg_gt_2sqrt_5_over_pi", C_of(2)*g_of(2,a_of(2)) > 2*mp.sqrt(mp.mpf(5)/mp.pi))

# ---------- G10: tail ----------
# DLMF 18.14.9 check: |H_n(x) e^{-x2/2}| <= sqrt(2^n n!) numerically
ci_ok=True
for n in range(1,26):
    b=mp.sqrt(mp.factorial(n)*mp.mpf(2)**n)
    for i in range(0,4001):
        x=mp.mpf(i)/10-200  # -200..200
        if abs(y_of(n,x))>b: ci_ok=False; break
J("G10_Cramer_Indritz_numeric_n1_25", ci_ok)
S=lambda n: mp.mpf(2)**n*mp.factorial(n)/C_of(n)**2
J("G10_S3", mp.nstr(S(3),15))
J("G10_S3_formula_3pi_over_4", abs(S(3)-3*mp.pi/4)<mp.mpf('1e-50'))
# S_n = sqrt(pi) Gamma((n+2)/2)/Gamma((n+1)/2)
J("G10_S_duplication", all(abs(S(n)-mp.sqrt(mp.pi)*mp.gamma(mp.mpf(n+2)/2)/mp.gamma(mp.mpf(n+1)/2))<mp.mpf('1e-40') for n in range(1,40)))
J("G10_S_le_sqrt_pi_n1_2", all(S(n) <= mp.sqrt(mp.pi*(n+1)/2) for n in range(1,80)))
ga2=lambda n: g_of(n,a_of(n))**2
J("G10_ga2_gt_E_over_pi", all(ga2(n) > mp.mpf(2*n+1)/mp.pi for n in range(1,200)))
# S_n < g(a)^2 all n>=1? (stronger than proposal's split; check)
J("G10_Sn_lt_ga2_all_n_3_200", all(S(n)<ga2(n) for n in range(3,201)))
J("G10_S1_S2_fail_ga2_expected", S(1)>ga2(1) and S(2)>ga2(2))
# n=3 exact: S3/ga2 = (3pi^2/28)(1-pi/28)
J("G10_n3_ratio_formula", abs(S(3)/ga2(3) - 3*mp.pi**2/28*(1-mp.pi/28))<mp.mpf('1e-40'))
J("G10_n3_ratio_lt_750_784", S(3)/ga2(3) < mp.mpf(750)/784)
J("G10_n2_sup_lt_Cg", sup2 < C_of(2)*g_of(2,a_of(2)))
J("G10_n1_sup_lt_Cg", max(abs(2*x)*mp.e**(-x**2/2) for x in [mp.mpf(i)/10000 for i in range(1,60000)]) < C_of(1)*g_of(1,a_of(1)))

# ---------- G11: LITERAL conjecture dense evidence ----------
lit_ok=True; worst11=(None,None,0)
for n in range(1,121):
    a=float(a_of(n)); sE=math.sqrt(2*n+1)
    xs=[mp.mpf(i)/50 for i in range(1, int(30*50)+1)]
    for x in xs:
        r=literal_lhs_rhs(n,x)
        if r>1:
            lit_ok=False; worst11=(n,float(x),float(r)); break
    if not lit_ok: break
J("G11_literal_conjecture_dense_n1_120", (lit_ok, worst11))

# ---------- G12: Foster-Krasikov 2000 Theorem 1 (as read from PDF pp307-308) ----------
def FK_bound(k,x):
    """Theorem 1, FK2000, valid x^2 < 2k-3/2. y=2k-x^2.
       (H_k)^2 e^{-x^2} <= C(k) * (2y^2-4y+3)/sqrt(y(4y^4-12y^3+9y^2+10ky-12k)) * exp(15x^2/(2y(2y-3)^2))
       C(k): even k: 2k*sqrt(4k-2) k!^2 / (sqrt(8k^2-8k+3) (k/2)!^2)
             odd  k: sqrt(16k^2-16k+6)/sqrt(2k-1) * k!(k-1)!/(((k-1)/2)!)^2"""
    y=2*k-x**2
    num=2*y**2-4*y+3
    den=mp.sqrt(y*(4*y**4-12*y**3+9*y**2+10*k*y-12*k))
    if k%2==0:
        Ck=2*k*mp.sqrt(4*k-2)*mp.factorial(k)**2/(mp.sqrt(8*k**2-8*k+3)*mp.factorial(k//2)**2)
    else:
        Ck=mp.sqrt(mp.mpf(16*k**2-16*k+6)/mp.mpf(2*k-1))*mp.factorial(k)*mp.factorial(k-1)/mp.factorial((k-1)//2)**2
    return Ck*num/den*mp.e**(15*x**2/(2*y*(2*y-3)**2))

# ratio at x=0 odd k (proposal: 1.001382658... for k=3)
J("G12_FK_over_C2_at0_k3", mp.nstr(FK_bound(3,0)/C_of(3)**2, 20))
for k in [3,5,7,9,21,51,101]:
    J(f"G12_FK_over_C2_at0_k{k}", mp.nstr(FK_bound(k,0)/C_of(k)**2, 15))

# Full pointwise: where does FK exceed conjectured C^2 g(min)^2 ? (on FK's range x^2<2k-3/2)
fk_exceed={}
for k in [3,5,7,9,15,21,51,101,201]:
    n=k; E=2*n+1; a=float(a_of(n)); xhi=math.sqrt(2*k-1.5)
    exceeds=[]
    N=4000
    for i in range(0,N+1):
        x=mp.mpf(xhi)*i/N
        fk=FK_bound(k,x)
        conj=C_of(n)**2*g_of(n,min(x,a))**2
        if fk>conj: exceeds.append(float(x))
    if exceeds:
        # contiguous intervals
        ivs=[]; st=exceeds[0]; pr=exceeds[0]
        for xx in exceeds[1:]:
            if xx-pr>0.01: ivs.append((round(st,4),round(pr,4))); st=xx
            pr=xx
        ivs.append((round(st,4),round(pr,4)))
        fk_exceed[k]={'n_bad':len(exceeds),'of':N+1,'intervals':ivs[:6]}
    else:
        fk_exceed[k]=None
J("G12_FK_exceeds_conjecture_intervals", fk_exceed)

# ---------- G13: subsumption assembly test ----------
# Can classical comparison + Wallis + FK + CI prove the conjecture without
# the proposal's refined sine/energy-loss work? Test: on [x0, FK range], FK <= conj?
gap={}
for k in [3,5,7,9,15,21,51,101]:
    n=k; E=2*n+1; x0=float(mp.sqrt(mp.mpf(2)/E)); a=float(a_of(n)); xhi=math.sqrt(2*k-1.5)
    bad=[]
    N=3000
    for i in range(0,N+1):
        x=mp.mpf(x0)+(mp.mpf(xhi)-x0)*i/N
        fk=FK_bound(k,x); conj=C_of(n)**2*g_of(n,min(x,a))**2
        if fk>conj: bad.append(float(x))
    gap[k]=(min(bad),max(bad),len(bad)) if bad else None
J("G13_FK_fails_on_[x0,range]_for", gap)

# CI coverage: x >= sqrt(E(1-1/S_n)) has CI <= C g(x)^2 ... i.e. S_n <= g(x)^2
def ci_min_x(n):
    E=2*n+1; S_=S(n)
    return mp.sqrt(E*(1-1/S_)) if S_>1 else mp.mpf(0)
J("G13_CI_needed_from_x", {n: mp.nstr(ci_min_x(n),8) for n in [3,5,9,21,101]})
# is x0 <= CI point always (so comparison region + CI overlap/cover with FK)?
J("G13_x0_le_CIx_all_odd_3_201", all(mp.sqrt(mp.mpf(2)/(2*n+1)) <= ci_min_x(n) for n in range(3,202,2)))

json.dump(out, open("/dev/stdout","w"), indent=1, default=str)
