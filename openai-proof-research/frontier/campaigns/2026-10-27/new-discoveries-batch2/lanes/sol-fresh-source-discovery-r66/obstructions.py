from fractions import Fraction as F
import json,pathlib
L=pathlib.Path(__file__).resolve().parent
x=F(11,10)
a=x**3+x+F(1001,1000000);da=3*x**3+x
b=F(1001,1000)*x**3+x*x+F(1,1000000);db=3*F(1001,1000)*x**3+2*x*x
D=2*db/b-da/a-3
assert D==F(-331808845,7206240054)
# Lambda=(1), n=3,t=1/2,x=2: exact Schur-Toda analogue failure.
x=F(2);c0=F(7,4);c1=x+F(3,4);c2=F(3,2)*x+F(1,4)
T=c1*c1/(c0*c2);lhs=x*F(3,4)/c1**2;rhs=2*x/(x-1)**2*(1-1/T)
assert lhs==F(24,121) and rhs==F(120,121)
(L/'obstructions.json').write_text(json.dumps({'positive_symmetric_mixture_log_slope':str(D),'toda_LHS':str(lhs),'toda_RHS':str(rhs),'toda_residual':str(lhs-rhs),'source_refutation':False},indent=2))
print((L/'obstructions.json').read_text())
