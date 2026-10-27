import sympy as s
u=s.symbols("u",nonnegative=True)
P3=1-4*u+10*u**2-20*u**3
P6=sum((-1)**j*s.binomial(5+j,j)*u**j for j in range(7))
assert s.expand(1-(1+u)**4*P3-u**4*(35+84*u+70*u**2+20*u**3))==0
assert s.expand((1+u)**6*P6-1-u**7*(792+3465*u+6160*u**2+5544*u**3+2520*u**4+462*u**5))==0
L=s.integrate(4*u**3*P3,(u,0,s.Rational(1,8)))
U=s.integrate(6*u**5*P6,(u,0,s.Rational(1,4)))
assert L==s.Rational(2291,13762560)
assert U==s.Rational(1574453,19377684480)
assert L-2*U==s.Rational(38411,9688842240)>0
print({"L":str(L),"U":str(U),"positive_midpoint_gap_lower_bound":str((L-2*U)/2),"status":"PASS exact algebra/integrals only; analytic substitution/source/novelty not verified by this script"})
