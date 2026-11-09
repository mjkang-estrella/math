from pathlib import Path
import sympy as s,json
z,w,t,u,L,x=s.symbols('z w t u L x');I=s.I
N=(w*z-w-1)*(w*z+w-1);Q=-w*w*z**3+2*w*w*z+4*w*z*z+2*w*z-w-3*z
M=s.Matrix([[-z,1,1,1,0],[1,-w,0,1,0],[1,0,-w,0,1],[1,1,0,-z,1],[0,0,1,1,-z]])
assert s.expand(M.det()-Q)==0 and s.expand(M.minor_submatrix(0,0).det()-N)==0
assert s.gcd(N,Q)==1
F=(L*(1-2*t*t)+t-t**3)*u*u+(-4*L-2*L*t+L*t*t-2*t)*u+3*L+t
assert s.expand(t*(N-L*Q).subs({z:1/t,w:t*u})-F)==0
p=1-t+t*t-t**3/2-t**4+(s.Rational(17,4)-1/(2*L))*t**5
res=s.Poly(s.expand(F.subs(u,p)),t)
assert all(res.nth(k)==0 for k in range(6))
p3=3+(3-2/L)*t
res3=s.Poly(s.expand(F.subs(u,p3)),t)
assert all(res3.nth(k)==0 for k in range(2))
R=(1-I*x-2*x*x+I*x**3)*w*w+(4*x-(2+2*I)*x*x-x**3)*w+3*x*x-I*x**3
assert s.expand(R-x**3*(Q-I*N).subs(z,-1/x))==0
print(json.dumps({'status':'PASS','checks':['determinant','cofactor','coprimality','generic-level clearing','slope-one residual through degree 5','slope-three residual through degree 1','R clearing']},indent=2))
