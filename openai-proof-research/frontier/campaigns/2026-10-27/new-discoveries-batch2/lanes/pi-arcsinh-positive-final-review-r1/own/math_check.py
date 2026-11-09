import sympy as sp
p,t,u,r = sp.symbols('p t u r', positive=True)
lp = sp.log
f = (1+t**p)**(-1/p)
# ell_p and ell_pp
H = lambda u: lp(1+u) - u*lp(u)/(1+u)
u_ = t**p
ell = -lp(1+t**p)/p
ell_p = sp.simplify(sp.diff(ell,p))
target = H(u_)/p**2
print("ell_p identity:", sp.simplify(ell_p-target)==0)
fpp = sp.simplify(sp.diff(f,p,2))
target2 = f/p**4*(H(u_)**2-2*p*H(u_)-p**3*(lp(t))**2*u_/(1+u_)**2)
print("f_pp identity:", sp.simplify(fpp-target2)==0)
# H bounds: H(1)=log2, H'(u)=-log u/(1+u)^2
Hp = sp.simplify(sp.diff(H(u),u)-( -lp(u)/(1+u)**2))
print("H' identity:", Hp==0)
print("H(1)=log2:", sp.simplify(H(1)-sp.log(2))==0)
# adjudication claim: generic vector f=(sum a_i^p)^(-1/p), f''/f=(H^2-2pH-p^3 Var_w(log a))/p^4
a1,a2 = sp.symbols('a1 a2', positive=True)
Z = a1**p+a2**p
w1=a1**p/Z; w2=a2**p/Z
Hn = -w1*lp(w1)-w2*lp(w2)
Var = w1*lp(a1)**2+w2*lp(a2)**2-(w1*lp(a1)+w2*lp(a2))**2
g = Z**(-1/p)
lhs = sp.simplify(sp.diff(g,p,2)/g)
rhs = (Hn**2-2*p*Hn-p**3*Var)/p**4
print("generic 2-pt f''/f identity:", sp.simplify(lhs-rhs)==0)
# numeric: concavity threshold p>log2/2 for A(p,x); and dim-5 counterexample direction (low p fails)
import mpmath as mp
def A(pv,x):
    return mp.quad(lambda tt:(1+tt**pv)**(-1/pv),[0,x])
x=0.7
for p0 in [0.4,0.5,sp.log(2)/2,0.4,1.0]:
    p0=float(p0)
    pm=0.9  # second point
    lam=0.5; mix=lam*A(p0,x)+(1-lam)*A(pm,x); mid=A(lam*p0+(1-lam)*pm,x)
    print(f"p0={p0:.3f} Jensen gap A(mid)-mix={float(mid-mix):.3e}")
# verify f''<0 for t=0.3, various p via formula
for pv in [0.4,0.5,0.35,0.4]:
    pv=float(pv); tv=0.3; u_=tv**pv
    Hval=mp.log(1+u_)-u_*mp.log(u_)/(1+u_)
    val=(1+u_)**(-1/pv)/pv**4*(Hval**2-2*pv*Hval-pv**3*(mp.log(tv))**2*u_/(1+u_)**2)
    print(f"t=0.3 p={pv}: f_pp={float(val):.4e} (neg={val<0}, threshold {float(mp.log(2)/2):.4f})")
