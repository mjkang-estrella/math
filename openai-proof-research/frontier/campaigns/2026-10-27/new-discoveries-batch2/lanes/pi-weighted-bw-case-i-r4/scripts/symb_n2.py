import sympy as sp

# Reduced variables, n=2, centered: x22 = -(w2/w1) x11, y22 = -(w2/w1) y11.
# Entries as (value, conjugate) symbol pairs.
x11,x12,x21 = sp.symbols('x11 x12 x21', complex=True)
c = sp.symbols('c', complex=True)  # conjugate bar symbol
def C(s): return sp.Symbol(str(s)+'bar', complex=True)
X11,X12,X21 = C(x11),C(x12),C(x21)
y11,y12,y21 = sp.symbols('y11 y12 y21', complex=True)
Y11,Y12,Y21 = C(y11),C(y12),C(y21)
w1,w2 = sp.symbols('w1 w2', positive=True)

x22 = -w2/w1*x11; X22 = -w2/w1*X11
y22 = -w2/w1*y11; Y22 = -w2/w1*Y11

# T_ij = sum_k w_k (X_{ik} Y_{kj} - Y_{ik} X_{kj})  (entries, no conj in products)
Xe = {(1,1):x11,(1,2):x12,(2,1):x21,(2,2):x22}
Ye = {(1,1):y11,(1,2):y12,(2,1):y21,(2,2):y22}
w = {1:w1, 2:w2}
T = {}
for i in (1,2):
    for j in (1,2):
        T[i,j] = sum(w[k]*(Xe[i,k]*Ye[k,j] - Ye[i,k]*Xe[k,j]) for k in (1,2))

# norm^2 with explicit conjugates
Xc = {(1,1):X11,(1,2):X12,(2,1):X21,(2,2):X22}
Yc = {(1,1):Y11,(1,2):Y12,(2,1):Y21,(2,2):Y22}
Tn2 = sum(T[i,j]*sp.Symbol(f'T{i}{j}bar') for i in (1,2) for j in (1,2))
# build conjugate map
conjugate = {}
for (v,cx) in [(x11,X11),(x12,X12),(x21,X21),(x22,X22),(y11,Y11),(y12,Y12),(y21,Y21),(y22,Y22)]:
    conjugate[v]=cx; conjugate[cx]=v
Tbar = {}
for i in (1,2):
    for j in (1,2):
        Tbar[i,j] = T[i,j].subs(conjugate)
Tn2 = sum(T[i,j]*Tbar[i,j] for i in (1,2) for j in (1,2))
nX2 = sum(Xe[i,j]*Xc[i,j] for i in (1,2) for j in (1,2))
nY2 = sum(Ye[i,j]*Yc[i,j] for i in (1,2) for j in (1,2))
s = w1**2+w2**2
D = sp.expand(s*nX2*nY2 - Tn2)

# ansatz: D = |alpha x11 Y11 + beta x12 Y12 + gamma x21 Y21|^2 ... but which Y-conj pairs?
# Solve for alpha,beta,gamma assuming psi = a*x11*Y11 + b*x12*Y12 + g*x21*Y21
a,b,g = sp.symbols('a b g', complex=True)
psi = a*x11*Y11 + b*x12*Y12 + g*x21*Y21
psibar = a.__class__ # placeholder
# conjugate of psi: a_bar X11 y11 + ...
ab,bb,gb = sp.symbols('ab bb gb', complex=True)
psib = ab*X11*y11 + bb*X12*y12 + gb*X21*y21
rhs = sp.expand(psi*psib)
# match coefficients: collect monomials
diff = sp.expand(D - rhs)
poly = sp.Poly(diff, x11,X11,x12,X12,x21,X21,y11,Y11,y12,Y12,y21,Y21, w1,w2)
# Solve coefficient equations for a,b,g,ab,bb,gb (a_bar=ab etc.)
eqs = []
for mon, coeff in poly.terms():
    eqs.append(sp.Eq(coeff, 0))
sol = sp.solve(eqs, [a,b,g,ab,bb,gb], dict=True)
print(len(sol))
if sol:
    print(sol[0])
