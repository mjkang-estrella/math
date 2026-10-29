import sympy as s,json
x,z=s.symbols('x z')
T=s.Matrix([[1+2*x,0,x*x,0],[1+x,x,0,x*x],[1+2*x,0,0,0],[1,2*x,0,0]])
a=s.Matrix([[1,2*x,0,0]]);b=s.Matrix([1+2*x,1+x,1+2*x,1])
F=s.factor((a*(s.eye(4)-z*T).inv()*b)[0]);num,den=s.fraction(F)
print('F(z,x)=',F)
print('num=',s.Poly(num,z));print('den=',s.Poly(den,z))
print('eigen poly=',T.charpoly().as_expr().factor())
# Signed minor prevents direct coefficientwise TP2 transfer argument.
for i in range(4):
 for j in range(i+1,4):
  for k in range(4):
   for l in range(k+1,4):
    v=s.expand(T.extract([i,j],[k,l]).det())
    if v!=0 and any(c<0 for c in s.Poly(v,x).all_coeffs()):print('negative minor',i,j,k,l,str(v));raise SystemExit
