import sympy as sp
r = sp.symbols('r', positive=True)
w1 = sp.symbols('w1', positive=True); w2 = r*w1
x11,x12,x21 = sp.symbols('x11 x12 x21')
def C(s): return sp.Symbol(str(s)+'b')
X11,X12,X21 = C(x11),C(x12),C(x21)
y11,y12,y21 = sp.symbols('y11 y12 y21')
Y11,Y12,Y21 = C(y11),C(y12),C(y21)
x22=-r*x11; X22=-r*X11; y22=-r*y11; Y22=-r*Y11
Xe={(1,1):x11,(1,2):x12,(2,1):x21,(2,2):x22}
Ye={(1,1):y11,(1,2):y12,(2,1):y21,(2,2):y22}
Xc={(1,1):X11,(1,2):X12,(2,1):X21,(2,2):X22}
Yc={(1,1):Y11,(1,2):Y12,(2,1):Y21,(2,2):Y22}
w={1:w1,2:w2}
T={}
for i in (1,2):
    for j in (1,2):
        T[i,j]=sp.expand(sum(w[k]*(Xe[i,k]*Ye[k,j]-Ye[i,k]*Xe[k,j]) for k in (1,2)))
conj={}
for (v,cx) in [(x11,X11),(x12,X12),(x21,X21),(x22,X22),(y11,Y11),(y12,Y12),(y21,Y21),(y22,Y22)]:
    conj[v]=cx; conj[cx]=v
Tn2=sum(T[i,j]*T[i,j].xreplace(conj) for i in (1,2) for j in (1,2))
nX2=sum(Xe[i,j]*Xc[i,j] for i in (1,2) for j in (1,2))
nY2=sum(Ye[i,j]*Yc[i,j] for i in (1,2) for j in (1,2))
D=sp.expand((w1**2+w2**2)*nX2*nY2 - Tn2)
F=sp.simplify(D/w1**2)
print("monomials:", len(sp.Add.make_args(F)))
for mon,co in sorted(sp.Poly(F, x11,X11,x12,X12,x21,X21,y11,Y11,y12,Y12,y21,Y21,r).terms()):
    print(mon, sp.factor(co))
