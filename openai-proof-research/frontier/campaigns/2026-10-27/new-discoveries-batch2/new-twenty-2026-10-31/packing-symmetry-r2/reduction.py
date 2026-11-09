import sympy as s
b,d,e=s.symbols('b d e');a=b*d
c=(2*b*(1-e)-d*d+e*e)/(2*(1-d))
F=2*a*d-a+b*b-2*b*d-2*b*e+2*b+2*c*e-2*c+1
print('Equal-active reduction, not a bound without case and domain proof:',flush=True)
print(s.factor(F),flush=True)
print('numerator after multiplying by 1-d:',s.Poly(s.cancel(F*(1-d)),e),flush=True)
