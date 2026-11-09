import sympy as sp
# Exact 1/x and 1/x^2 coefficients of T(x)=int_x^inf t^-nu K_mu(t)dt and x^-nu K_eta(x)
nu, mu = sp.symbols("nu mu", positive=True)
a = (4*mu**2-1)/8; b = (4*mu**2-1)*(4*mu**2-9)/128
alpha = nu + sp.Rational(1,2)
c1T = a - alpha
c2T = alpha*(alpha+1) - a*(alpha+1) + b
eta = sp.symbols("eta", positive=True)
ap = (4*eta**2-1)/8; bp = (4*eta**2-1)*(4*eta**2-9)/128
# substitute delta^2 = mu^2-2nu-1 for T coefficients
d2 = mu**2-2*nu-1
c1T_d = sp.simplify(c1T.subs(mu**2, d2+2*nu+1))
print("c1T in delta:", sp.simplify((4*d2-1)/8 - c1T), "(should be 0)")
# numeric check params n=0.3,nu=3.4 -> mu=3.7
vals = {nu: sp.Rational(34,10), mu: sp.Rational(37,10), eta: sp.sqrt(sp.Rational(37,10)**2-2*sp.Rational(34,10)-1)+1}
print("c1T =", sp.N(c1T.subs(vals),20), " c2T =", sp.N(c2T.subs(vals),20))
print("c1K =", sp.N(ap.subs(vals),20), " c2K =", sp.N(bp.subs(vals),20))
