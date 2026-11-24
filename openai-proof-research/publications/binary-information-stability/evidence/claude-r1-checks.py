# Independent checks for claude-manuscript-audit-r1 (sanity evidence, not proofs).
import sympy as sp, mpmath as mp, random, itertools
mp.mp.dps = 30
random.seed(20261013)
out = []
def rep(name, ok, extra=""):
    out.append(f"{'PASS' if ok else 'FAIL'}  {name}  {extra}")

x, y, t, a, r, m, b, d, A, rho, z, kap, h = sp.symbols('x y t a r m b d A rho z kappa h', real=True)
psi = lambda u: ((1+u)*sp.log(1+u) + (1-u)*sp.log(1-u))/2
H = lambda u: sp.log(2) - psi(u)
V = sp.atanh

# 1. reserve ray Euler identity A J_A - J = kappa, m=1-A, d=rho*A
J = H(1-A) - (H(1-A+rho*A) + H(1-A-rho*A))/2
kappa_expr = -sp.Rational(1,2)*sp.log(1 - (rho*A)**2/(2-A)**2)
expr = A*sp.diff(J, A) - J - kappa_expr
vals = [expr.subs({A: sp.Rational(p,10), rho: sp.Rational(q,10)}).evalf(30) for p in (2,5,8) for q in (1,3,4) if (1-sp.Rational(p,10)) + sp.Rational(q,10)*sp.Rational(p,10) < 1]
rep("reserve Euler A*J_A - J = kappa (numeric 30 digits)", max(abs(v) for v in vals) < 1e-25, f"max={max(abs(v) for v in vals)}")

# 2. thinning path derivatives lambda I' = I - A*, lambda nu' = nu - A* - kappa
lam, xc, dc = sp.symbols('lam xc dc', positive=True)
xx = 1 - lam*(1-xc); dd = lam*dc; hc = (H(xc+dc)+H(xc-dc))/2; ee = lam*hc
I_ = H(xx) - ee; nu_ = (H(xx+dd)+H(xx-dd))/2 - ee
Astar = sp.log(2/(1+xx)); kap_ = -sp.Rational(1,2)*sp.log(1-dd**2/(1+xx)**2)
e1 = lam*sp.diff(I_, lam) - (I_ - Astar); e2 = lam*sp.diff(nu_, lam) - (nu_ - Astar - kap_)
mx = 0
for (l, xcv, dcv) in [(0.3,0.1,0.2),(0.7,0.4,0.3),(0.95,0.0,0.6),(0.5,0.6,0.2)]:
    s = {lam: sp.Float(l,30), xc: sp.Float(xcv,30), dc: sp.Float(dcv,30)}
    mx = max(mx, abs(e1.subs(s).evalf(30)), abs(e2.subs(s).evalf(30)))
rep("thinning path derivative identities", mx < 1e-25, f"max={mx}")

# 3. K0'(a) sign vs 1 - t coth t + t^2 sech^2 t
K0 = psi(a) + sp.log(a + (1-a**2)*V(a)) - sp.log(2*a)
dK0 = sp.diff(K0, a)
ok = True
for tv in [0.1,0.5,1.0,1.5,2.0,3.0]:
    av = mp.tanh(tv)
    lhs = sp.N(dK0.subs(a, sp.Float(str(av),30)), 30)
    rhs = 1 - tv*mp.coth(tv) + tv**2*mp.sech(tv)**2
    ok &= (sp.sign(lhs) == sp.sign(sp.Float(str(rhs))))
rep("sign K0' = sign(1 - t coth t + t^2 sech^2 t) at sample t", ok)
# crossing of ratio=1 and K0>0 on grid
mn = min(mp.mpf(sp.N(K0.subs(a, sp.Float(i/1000,30)),30)) for i in range(1,1000))
rep("K0(a)>0 on (0,1) grid", mn > 0, f"min={mp.nstr(mn,5)}")

# 4. scalar strict inequality k > r^2(1-b)/(1-r^2 b) on grid incl. near corners
def psin(u): return ((1+u)*mp.log(1+u)+(1-u)*mp.log(1-u))/2
worst = mp.inf
for av in [mp.mpf(i)/200 for i in range(1,200)] + [1-mp.mpf(10)**-6]:
    for rv in [mp.mpf(j)/200 for j in range(1,200)]:
        k = rv*mp.atanh(rv*av)/mp.atanh(av); bb = mp.e**psin(av)-1
        g = (k - rv**2*(1-bb)/(1-rv**2*bb))/(rv**2*(1-rv**2))
        worst = min(worst, g)
rep("k - r^2(1-b)/(1-r^2 b) > 0 (normalized) on 200x200 grid", worst > 0, f"min={mp.nstr(worst,5)}")

# 5. quartic bracket identity
C4 = (1+3*m**2)/(12*h**3)
br = C4*h**2*(3-2*kap) - sp.Rational(1,12) - m**2*(1-kap)/h
claim = kap*m**2/(3*h) + (1-kap)/6
rep("normal-form bracket identity (h=1-m^2)", sp.simplify((br-claim).subs(h,1-m**2)) == 0)
lowb = sp.simplify((claim - (m**2+1-kap)/12).subs(h,1-m**2))
ok = all(lowb.subs({m: sp.Rational(i,10), kap: sp.Rational(j,10)}) >= 0 for i in range(0,10) for j in range(0,11))
rep("bracket >= (m^2+1-kappa)/12 on grid", ok)

# 6. psi expansions: one-bit information series and sharpness
Ib = sp.series((psi(m+b)+psi(m-b))/2 - psi(m), b, 0, 6).removeO()
target = b**2/(2*(1-m**2)) + (1+3*m**2)*b**4/(12*(1-m**2)**3)
rep("I(m+bX) series to b^4", sp.simplify(Ib - target) == 0)
hh = 1-m**2
b2 = hh*a**2 - sp.Rational(2,3)*m**2*a**4
Iin = (b2/(2*hh) + (1+3*m**2)*b2**2/(12*hh**3))
rep("b(a)^2 normalization to a^4", sp.simplify(sp.expand(sp.series(Iin - (a**2/2 + a**4/12), a, 0, 6).removeO())) == 0)
Iout = (r**2*b2/(2*hh) + (1+3*m**2)*r**4*b2**2/(12*hh**3))
Del = sp.series((r**2*a**2/2 + r**4*a**4/12) - Iout, a, 0, 6).removeO()
rep("one-bit deficit r^2(1-r^2)m^2 a^4/(3h)", sp.simplify(Del - r**2*(1-r**2)*m**2*a**4/(3*hh)) == 0)
rep("psi(ra)-r^2 psi(a) = -r^2(1-r^2)a^4/12 + O(a^6)", sp.simplify(sp.series(psi(r*a)-r**2*psi(a),a,0,6).removeO() + r**2*(1-r**2)*a**4/12) == 0)

# 7. Q11 expansion
kser = sp.series(r*V(r*a)/V(a), a, 0, 4).removeO()
rep("k = r^2 - r^2(1-r^2)a^2/3 + O(a^4)", sp.simplify(kser - (r**2 - r**2*(1-r**2)*a**2/3)) == 0)
pp = lambda u: 1/(1-u**2)
Ein = sp.series((pp(m+b)+pp(m-b))/2, b, 0, 4).removeO()
Eout = sp.series((pp(m+r*b)+pp(m-r*b))/2, b, 0, 4).removeO()
Q11 = sp.expand(kser*Ein - r**2*Eout)
Q11c = r**2*(1-r**2)*((1+3*m**2)*b**2/(1-m**2)**3 - a**2/(3*(1-m**2)))
# compare second-order part (a^2, b^2 terms); drop a^2 b^2 and higher
diff = sp.expand(sp.simplify(Q11 - Q11c))
poly = sp.Poly(sp.together(diff).as_numer_denom()[0], a, b)
low = [mon for mon in poly.monoms() if sum(mon) <= 2 and poly.coeff_monomial(a**mon[0]*b**mon[1]) != 0]
rep("Q11 leading expansion", low == [], f"residual low monomials={low}")
rep("Q11 at m=0,b=a coefficient 2r^2(1-r^2)/3", sp.simplify(Q11c.subs({m:0,b:a})/a**2 - 2*r**2*(1-r**2)/3) == 0)

# 8. Lemma local constant coefficient a^2 q, and sharpness coefficient
kk = sp.Symbol('k')
q = kk/(1-a**2) - r**2/(1-r**2*a**2)
rep("constant Walsh coefficient = a^2 q", sp.simplify(kk/(1-a**2) - 1/(1-r**2*a**2) + 1 - kk - a**2*q) == 0)
rep("phi'(t) for (1-t^2)V/t", sp.simplify(sp.diff((1-t**2)*V(t)/t, t) - (t - (1+t**2)*V(t))/t**2) == 0)

# 9. Hessian determinant of G
c, Jv = sp.symbols('c J', positive=True)
Fpp = sp.Symbol('Fpp')
Hs = sp.Matrix([[2*c*Jv**2, 4*c*m*Jv],[4*c*m*Jv, Fpp + 2*c*m**2]])
rep("det Hess G", sp.simplify(Hs.det() - 2*c*Jv**2*(Fpp - 6*c*m**2)) == 0)

# 10. scalar constants: F via parametrisation I=psi(r), F=rV(r)
L = mp.log(2); M = 4*L**2/3; delta0 = 2-3*M
def Fpp_of_r(rr):
    Vv = mp.atanh(rr); return ((1+rr**2)*Vv - rr)/((1-rr**2)**2*Vv**3)
def Fp_of_r(rr):
    v = mp.atanh(rr); return 1 + mp.sinh(2*v)/(2*v)
def r_of_I(I): return mp.findroot(lambda rr: psin(rr)-I, (mp.mpf('1e-12'), 1-mp.mpf('1e-20')), solver='bisect') if I>0 else mp.mpf(0)
grid = [L/2*i/400 for i in range(1,401)]
ratio = max(Fpp_of_r(r_of_I(I))/Fp_of_r(r_of_I(I)) for I in grid)
ratio = max(ratio, mp.mpf(4)/3/2)  # value at I=0: F''(0)/F'(0)=2/3
eta = 2 - ratio
k0 = L - mp.mpf(1)/2
Xi = mp.quad(lambda s: (s-k0)*Fpp_of_r(r_of_I(s)) if s>0 else (s-k0)*mp.mpf(4)/3, [0, k0, L/2])
mu = mp.mpf(4)/3; B1 = delta0/8; C1 = 4*L**2 + 3*L/2
cval = min(mu/8, B1/C1, eta, Xi/L**2)/2
rep("delta0=2-4L^2>0", delta0 > 0, f"delta0={mp.nstr(delta0,6)}")
rep("eta>0", eta > 0, f"eta~{mp.nstr(eta,6)}")
rep("Xi(L/2)>0", Xi > 0, f"Xi(L/2)~{mp.nstr(Xi,6)}")
rep("c value (eq:c)", cval > 0, f"c~{mp.nstr(cval,6)}; binding={'B1/C1' if cval==B1/C1/2 else 'other'}")
rep("L^2+L/4 > M", L**2 + L/4 > M, f"{mp.nstr(L**2+L/4,6)} vs {mp.nstr(M,6)}")

# 11. E_lambda bound and (added) inequality on random states
worst1 = mp.inf; worst2 = mp.inf
def hb(p): return -p*mp.log(p)-(1-p)*mp.log(1-p) if 0<p<1 else mp.mpf(0)
def Hn(u): return L - psin(u)
for _ in range(20000):
    xcv = mp.mpf(random.random())*0.98; dcv = mp.mpf(random.random())*(1-xcv)*0.999 + mp.mpf('1e-6')
    lv = mp.mpf(random.random())*0.999 + mp.mpf('1e-4')
    sc = 1-xcv
    El = hb(lv*sc/2) - lv*hb(sc/2)
    worst1 = min(worst1, mp.mpf(3)/4*lv*sc*mp.log(1/lv) - El)
    xv = 1 - lv*sc; dv = lv*dcv; ev = lv*(Hn(xcv+dcv)+Hn(xcv-dcv))/2
    Iv = Hn(xv)-ev; nuv = (Hn(xv+dv)+Hn(xv-dv))/2 - ev
    Jc = Hn(xcv) - (Hn(xcv+dcv)+Hn(xcv-dcv))/2
    lhs = xv**2*(Iv**2-nuv**2); rhs = 4*lv*xcv**2*Jc**2 + C1*lv*(1-lv)*dcv**2
    worst2 = min(worst2, (rhs-lhs)/(rhs+mp.mpf('1e-300')))
rep("E_lambda <= (3/4) lambda sigma_c log(1/lambda) (20000 random)", worst1 >= -1e-25, f"min slack={mp.nstr(worst1,5)}")
rep("(eq:added) x^2(I^2-nu^2) <= 4 lam xc^2 Jc^2 + C1 lam(1-lam) dc^2 (20000 random)", worst2 >= 0, f"min rel slack={mp.nstr(worst2,5)}")

# 12. newcorner: lam*c_c >= G(x,I)-G(x,nu) with c from (eq:c)
def Fof(I):
    if I <= 0: return mp.mpf(0)
    rr = r_of_I(I); return rr*mp.atanh(rr)
def cost(p, q_): return (p-q_)/4*(mp.atanh(p)-mp.atanh(q_))
worst3 = mp.inf
for _ in range(3000):
    xcv = mp.mpf(random.random())*0.95; dcv = mp.mpf(random.random())*(1-xcv)*0.99 + mp.mpf('1e-4')
    lv = mp.mpf(random.random())*0.999 + mp.mpf('1e-3')
    xv = 1 - lv*(1-xcv); dv = lv*dcv; ev = lv*(Hn(xcv+dcv)+Hn(xcv-dcv))/2
    Iv = Hn(xv)-ev; nuv = (Hn(xv+dv)+Hn(xv-dv))/2 - ev
    lhs = lv*cost(xcv+dcv, xcv-dcv)
    rhs = Fof(Iv) + cval*xv**2*Iv**2 - Fof(nuv) - cval*xv**2*nuv**2
    worst3 = min(worst3, lhs - rhs)
rep("(eq:newcorner) on 3000 random thinning states", worst3 >= 0, f"min slack={mp.nstr(worst3,5)}")

# 13. Theorem 1.3 on random interior fields, n<=4 (exact production)
def field_stats(vals, n):
    N = len(vals); mean = sum(vals)/N
    Iu = sum(psin(v) for v in vals)/N - psin(mean)
    D = mp.mpf(0)
    for idx in range(N):
        for i in range(n):
            j = idx ^ (1<<i)
            D += (vals[idx]-vals[j])*(mp.atanh(vals[idx])-mp.atanh(vals[j]))
    D /= (4*N)
    return mean, Iu, D
worst4 = mp.inf
for _ in range(400):
    n = random.choice([1,2,3,4]); base = random.uniform(-0.95,0.95); spread = random.uniform(0,1)
    vals = [mp.mpf(max(-0.999,min(0.999, base + spread*random.uniform(-1,1)))) for _ in range(2**n)]
    mean, Iu, D = field_stats(vals, n)
    if Iu <= 1e-12: continue
    worst4 = min(worst4, D - Fof(Iu) - cval*mean**2*Iu**2)
rep("Thm 1.3 D >= F(I)+c m^2 I^2 on 400 random fields n<=4", worst4 >= 0, f"min slack={mp.nstr(worst4,5)}")

open(__file__.replace('.py','.out'),'w').write("\n".join(out)+"\n")
print("\n".join(out))
