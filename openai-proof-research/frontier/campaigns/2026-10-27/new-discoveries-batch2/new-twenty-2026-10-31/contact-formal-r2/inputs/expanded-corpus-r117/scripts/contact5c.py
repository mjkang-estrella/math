import sympy as s
z,w,t,l=s.symbols('z w t l');A=s.Matrix([[-z,1,1,1,0],[1,-w,0,1,0],[1,0,-w,0,1],[1,1,0,-z,1],[0,0,1,1,-z]])
f=s.factor(A.minor_submatrix(0,0).det()/A.det());print('f=',f)
num=s.fraction(s.cancel(f-l))[0];print('level polynomial=',s.factor(num));p=s.Poly(s.expand(num.subs(z,1/t)*t**3),w);print('t-polynomial=',p.as_expr())
for w0 in [1,3]:
 for lv in [1,2]:
  cs=s.symbols('c1:7'); ws=t*(w0+sum(cs[i-1]*t**i for i in range(1,7)));pol=s.Poly(s.expand(p.as_expr().subs({w:ws,l:lv})),t); sol={}
  for i,c in enumerate(cs):
   q=s.expand(pol.nth(i+3).subs(sol));r=s.solve(q,c);sol[c]=r[0] if r else 0
  print('branch',w0,'level',lv,sol)
