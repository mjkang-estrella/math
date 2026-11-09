# Rigorous interval bounds for the 344302 proof (mpmath interval arithmetic, outward rounding).
# Notation: A(x) = 1/f(x) = sum a_L x^L, f(x) = sum_m c_m x^m/m!, c = (1,-1,0) periodic;
# f(x) = (2/sqrt3) e^{-x/2} sin(pi/3 - sqrt3 x/2); poles z_k = x0(1+3k), x0 = 2pi/(3 sqrt3);
# e_j = (-1)^j e^{z_j/2}/z_j; P(x) = e_0/(1-x/z_0) + e_{-1}/(1-x/z_{-1}); H = A - P analytic in |x| < 4x0.
import sys, json
sys.path.append('/home/mj-kang/.local/lib/python3.14/site-packages')
import mpmath as mp
from mpmath import iv
from fractions import Fraction
from math import factorial
sys.path.insert(0, sys.argv[1])
from dd344302 import dd_single
iv.dps = 40
PI = iv.pi; S3 = iv.sqrt(3)
x0 = 2*PI/(3*S3)
e0 = iv.exp(x0/2)/x0
em1 = iv.exp(-x0)/(2*x0)
out = {}
# ---- (1) max |A(x)| and |H(x)| on circle |x| = r = 3 x0, by subdividing theta in [0, pi] (A(conj x) = conj A(x)).
r = 3*x0
NARC = int(sys.argv[2])
MA = iv.mpf(0); MH = iv.mpf(0)
for k in range(NARC):
    th = iv.mpf([mp.mpf(k)/NARC, mp.mpf(k+1)/NARC])*PI
    x_re = r*iv.cos(th); x_im = r*iv.sin(th)
    # w = pi/3 - sqrt3 x/2 ; |sin w|^2 = sin^2(Re w) + sinh^2(Im w)
    w_re = PI/3 - S3*x_re/2; w_im = -S3*x_im/2
    sh = (iv.exp(w_im) - iv.exp(-w_im))/2
    sin2 = iv.sin(w_re)**2 + sh**2
    absA = (S3/2)*iv.exp(x_re/2)/iv.sqrt(sin2)
    # |P(x)| <= e0/|1-x/x0| + em1/|1+x/(2x0)|, with |1-x/x0| >= |x|/x0 - 1 = 2 ; |1 + x/(2x0)| >= 3/2 - 1 = 1/2
    absP = e0/2 + em1*2
    MA = iv.mpf([0, max(MA.b, absA.b)])
    MH = iv.mpf([0, max(MH.b, (absA + absP).b)])
out['circle_r_over_x0'] = 3
out['max_abs_A_on_circle_upper'] = str(MA.b)
out['max_abs_H_on_circle_upper'] = str(MH.b)
# ---- (2) T^abs(u,v) = sum_{s,t} u^s v^t/(s+t+3)!  (upper bound, series with explicit tail)
def Tabs(u, v, M=120):
    s = iv.mpf(0)
    for m in range(M):
        # sum_{s+t=m} u^s v^t <= (m+1) max(u,v)^m
        s += (m+1)*iv.mpf(max(u.b, v.b))**m/iv.factorial(m+3)
    tail = (M+1)*iv.mpf(max(u.b, v.b))**M/iv.factorial(M+3)*2  # crude: ratio of successive terms < 1/2 here
    return s + tail
TA = Tabs(r, x0)
# E1(p) := e0 x0^p ([x^p] H T(.,x0) - x0 [x^{p+1}] H T(.,x0)); Cauchy: |[x^m] H T| <= MH * Tabs(r,x0) / r^m
C1 = e0*MH*TA*(1 + x0/r)      # => |E1(p)| <= C1 * 3^{-p}
out['C1_upper'] = str(C1.b)
# ---- (3) exact rational a_L, and rigorous U_p(x0) for p <= P1
P1 = int(sys.argv[3])
aF = [Fraction(dd_single(L, -1) if L else 1, factorial(L)) for L in range(P1+3)]
def kappa(s, z, M=60):
    cs = (1, -1, 0)[s % 3]
    if cs == 0: return iv.mpf(0)
    tot = iv.mpf(0)
    for t in range(M):
        ct = (1, -1, 0)[t % 3]
        if ct: tot += cs*ct*z**t/iv.factorial(s+t+3)
    tail = 2*abs(z)**M/iv.factorial(s+M+3)
    return tot + iv.mpf([-tail.b, tail.b])
def W(p, z):
    return sum((iv.mpf(aF[p-s].numerator)/aF[p-s].denominator)*kappa(s, z) for s in range(p+1))
tau = None
res = []
ok = True
for p in range(P1+1):
    U = W(p, x0) - x0*W(p+1, x0)
    val = e0*U*x0**p*(-1)**p   # should be > 0
    main = (iv.mpf(3)/2)*(iv.mpf(1)/2)**p
    res.append({'p': p, 'signed_value_lower': str(val.a), 'signed_value_upper': str(val.b)})
    if not val.a > 0: ok = False
out['U_p_signs_positive_for_all_p_le_P1'] = ok
out['U_p'] = res
# tau = e0 em1 T(-2x0, x0)
def Texact(x, y, M=70):
    tot = iv.mpf(0)
    for s in range(M):
        for t in range(M - s):
            cc = (1, -1, 0)[s % 3]*(1, -1, 0)[t % 3]
            if cc: tot += cc*x**s*y**t/iv.factorial(s+t+3)
    mx = iv.mpf(max(abs(x).b, abs(y).b))
    tail = iv.mpf(0)
    for m in range(M, M+400): tail += (m+1)*mx**m/iv.factorial(m+3)
    tail += 2*(M+401)*mx**(M+400)/iv.factorial(M+403)   # omitted terms with s+t >= M, geometric tail
    return tot + iv.mpf([-abs(tail).b, abs(tail).b])
tau = e0*em1*Texact(-2*x0, x0)
out['tau_lower'] = str(tau.a); out['tau_upper'] = str(tau.b)
out['e0'] = [str(e0.a), str(e0.b)]; out['e_minus1'] = [str(em1.a), str(em1.b)]
# smallest p beyond which (3/2) tau 2^{-p} * (1/2) > 2*C1*3^{-p}  (so the two-mode main term dominates E1 with margin)
p = 0
while not ((iv.mpf(3)/4)*tau*(iv.mpf(1)/2)**p).a > (2*C1*(iv.mpf(1)/3)**p).b: p += 1
out['p_threshold_main_dominates_E1'] = p
print(json.dumps(out, indent=1))
# ---- (4) remaining constants and case-B threshold
K0 = e0 + em1 + MH                     # sup_m a_m x0^m (Cauchy on |x|=3x0: a_m = e0 x0^-m + em1 (-2x0)^-m + h_m, |h_m|<=MH r^-m)
C2 = 3*K0*Tabs(x0, 2*x0)               # |x0^p U_p(-2x0)| <= C2
C3 = MH*K0*Tabs(x0, r)*4               # |x0^{p+q} R(p,q)| <= C3 3^-q
C1pp = em1*MH*Tabs(r, 2*x0)*(iv.mpf(5)/3)  # |mirror x-H error| <= C1pp 2^-q 3^-p
# truncation: |eps_j(p,z)| <= sum_{s>p} |z_j|^s sum_t |z|^t/(s+t+3)! ; normalized contributions bounded by
def trunc(p, zj, z):
    # sum_{s>p} |zj|^s sum_t |z|^t/(s+t+3)! <= sum_{s>p} |zj|^s e^{|z|}/(s+3)!, summed to s=p+200 plus geometric tail
    tot = iv.mpf(0)
    for s in range(p+1, p+201):
        tot += abs(zj)**s*iv.exp(abs(z))/iv.factorial(s+3)
    last = abs(zj)**(p+200)*iv.exp(abs(z))/iv.factorial(p+203)
    return tot + 2*last
out['K0_upper'] = str(K0.b); out['C2_upper'] = str(C2.b); out['C3_upper'] = str(C3.b); out['C1pp_upper'] = str(C1pp.b)
pB = None
for p in range(0, 200):
    # normalized truncation errors (j=0 in U_p(x0): e0*(|eps_0(p+1,x0)|+|eps_0(p,x0)|) ; j=-1: em1*2^-p*(...)*x0^p... crude bound below)
    tr = e0*e0*(trunc(p, x0, x0) + trunc(p+1, x0, x0)) \
         + e0*em1*(trunc(p, 2*x0, x0) + trunc(p+1, 2*x0, x0))*(iv.mpf(1)/2)**p \
         + em1*e0*(trunc(p, x0, 2*x0) + 2*trunc(p+1, x0, 2*x0)) \
         + em1*em1*(trunc(p, 2*x0, 2*x0) + trunc(p+1, 2*x0, 2*x0))*(iv.mpf(1)/2)**p
    # y-side truncation in [y^q] e_l/(1-y/z_l) W_p(y): normalized bound for l in {0,-1}, for D(p,q) and D(p+1,q-1), q >= p+2
    qq = p + 1   # smallest exponent appearing is q-1 >= p+1
    ytr = 2*K0*iv.exp(x0)*(e0*trunc(qq-1, x0, iv.mpf(0)) + em1*trunc(qq-1, 2*x0, iv.mpf(0)))
    tr = tr + ytr
    lhs = (iv.mpf(3)/4)*tau*(iv.mpf(1)/2)**p
    rhs = C1*(iv.mpf(1)/3)**p + C1pp*(iv.mpf(1)/4)*(iv.mpf(1)/3)**p + C3*(iv.mpf(1)/3)**(p+2) + tr
    if lhs.a > rhs.b:
        pB = p; break
out['caseB_threshold_p'] = pB
out['note'] = 'Case B valid for p >= caseB_threshold_p (all q >= p+2); Case A uses rigorous U_p(x0) signs for p <= P1 and q >= 198-P1 with mirror/R bounds.'
# Case A check: for p <= P1, q >= 198 - P1: signed U_p lower bound > em1*C2*2^-q + C3*3^-q
qmin = 198 - P1
ytrA = 2*K0*iv.exp(x0)*(e0*trunc(qmin-2, x0, iv.mpf(0)) + em1*trunc(qmin-2, 2*x0, iv.mpf(0)))
caseA = all(iv.mpf(rr['signed_value_lower']).a > (em1*C2*(iv.mpf(1)/2)**qmin + C3*(iv.mpf(1)/3)**qmin + ytrA).b for rr in res)
out['caseA_ok'] = caseA
print(json.dumps({k: out[k] for k in ['K0_upper', 'C2_upper', 'C3_upper', 'C1pp_upper', 'caseB_threshold_p', 'caseA_ok']}, indent=1))
