import sympy as S
u,v,t=S.symbols('u v t', positive=True)
f=1/u**2+1/v**2-8/(u+v)**2
factor=(u-v)**2*(u*u+4*u*v+v*v)/(u*u*v*v*(u+v)**2)
assert S.cancel(f-factor)==0
print('factorization residual',S.cancel(f-factor))
print('normalization',(64+1+64)/S.Integer(129))
H=S.hessian(32*f/129,(u,v)).subs({u:1,v:1});print('gap Hessian',H)
assert H==S.Matrix([[32,-32],[-32,32]])/43
m=S.Matrix([8,-1+t,8]);A=S.Matrix([[0,-2,-S.Rational(1,2)],[-2,0,-2],[-S.Rational(1,2),-2,0]])
Et=S.factor((m.T*A*m)[0]/(m.dot(m)));print('normalized mass path energy',Et)
assert S.cancel(Et+64*t/(129-2*t+t*t))==0
print('transverse exponent 2 energy',S.factor(S.Rational(64,129)*(1/(1+t*t)-1)))
print('all exact checks passed')
