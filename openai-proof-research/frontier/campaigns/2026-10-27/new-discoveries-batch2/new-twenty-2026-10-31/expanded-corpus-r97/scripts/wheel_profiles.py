import itertools,json,pathlib,math
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for t in range(2,41):
 m=2*t+1;profiles=[(1,0,t*m)];slack=[]
 for a in range(t+1):
  for b in range(t+1):
   if a and b:r=((m-a)*(m-b)+(a-1)*(b-1))//2
   elif a+b:r=t*(m-a-b)
   else:r=t*m
   p=(0,a+b,r);profiles.append(p);slack.append(2*(2*t*t+t+1)-(t+1)*(a+b)-2*r)
 assert min(slack)>=0
 # source three equalities; fractional cover using orbit averages. p=(hub,mixed,rim).
 # weights lambda for averaged independent sets ensure each vertex total>=1.
 # 3x3 exact solve via sympy
 import sympy as s
 P=s.Matrix([[1,0,0],[0,2,2*t],[t*m,2*t*t,t*t+1]]);sizes=s.Matrix([1,2*m,m*m]);lam=P.inv()*sizes;chi=sum(lam);expected=Fraction(6*t*t+7*t+3,2*t*t+t+1)
 assert all(v>=0 for v in lam) and chi==s.Rational(expected.numerator,expected.denominator)
 out.append({'t':t,'profiles':profiles,'min_slack':min(slack),'orbit_cover_coefficients':[str(v) for v in lam],'chi':str(chi)})
(D/'outputs/wheel-profiles.json').write_text(json.dumps(out,indent=2)+'\n');print('verified closed profile optimization and fractional-cover coefficients t=2..40')
