from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path
L=Path(__file__).resolve().parent
count=0;bad=[]
for m in range(2,9):
 for rates in combinations(range(1,13),m):
  cs=[]
  for a in rates:
   c=Q(a)
   for b in rates:
    if a!=b:c*=Q(b,b-a)
   cs.append(c)
  d=[sum(c*(-a)**k*Q(1,2**a) for a,c in zip(rates,cs)) for k in range(5)]
  f,f1,f2,f3,f4=d
  assert f>0
  n=-f4*f**3+4*f3*f1*f**2+3*f2**2*f**2-12*f2*f1**2*f+6*f1**4
  count+=1
  if n<0:bad.append({'rates':rates,'numerator':str(n),'vpp':str(n/f**4)})
# A generic strictly log-concave, Gaussian-tail density does NOT have the sharp center bound:
# h=x^2+exp(-x^2): h''=2+(4x^2-2)exp(-x^2), minimum zero at 0;
# instead h=x^2-eps*cos(x), eps=1: h''=2+cos(x) in [1,3], center3, at pi1.
# f proportional exp(-x^2+cos x), w0=3, w(pi)=1; exact symbolic checks below.
import sympy as s
x=s.symbols('x',real=True);h=x*x-s.cos(x)
w=s.diff(h,x,2)
assert w.subs(x,0)==3 and w.subs(x,s.pi)==1
# verify derivative polynomial and differentiated convolution expressions symbolically
G=s.Function('G')(x)
v=-s.diff(s.log(G),x,2)
expr=(-s.diff(G,x,4)*G**3+4*s.diff(G,x,3)*s.diff(G,x)*G**2+3*s.diff(G,x,2)**2*G**2-12*s.diff(G,x,2)*s.diff(G,x)**2*G+6*s.diff(G,x)**4)/G**4
assert s.simplify(s.diff(v,x,2)-expr)==0
# independent exact differentiation of hypoexponential polynomial in y=e^-t for selected cases
y=s.symbols('y',positive=True)
checks=0
for rates in [(1,2),(1,3,8),(2,5,7,11),(1,2,4,8,12)]:
 p=sum(s.Rational(a)*s.prod(s.Rational(b,b-a) for b in rates if b!=a)*y**a for a in rates)
 logp=s.log(p)
 for k in range(4):logp=-y*s.diff(logp,y)
 direct=-logp.subs(y,s.Rational(1,2))
 ds=[]
 for k in range(5):
  q=p
  for j in range(k):q=-y*s.diff(q,y)
  ds.append(q.subs(y,s.Rational(1,2)))
 a,b,c,d,e=ds
 poly=(-e*a**3+4*d*b*a*a+3*c*c*a*a-12*c*b*b*a+6*b**4)/a**4
 assert s.simplify(poly-direct)==0;checks+=1
out={'hypoexponential_exact_cases':count,'negative_cases':bad,'independent_symbolic_cases':checks,'generic_strong_logconcavity_obstruction':{'potential':'x^2-cos(x)','w0':3,'w_pi':1},'status':'finite checks only, not all-rates or Airy theorem'}
(L/'exact-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
# Stronger exact obstruction sharing the public theorem's curvature lower bound.
h=x**4+x*x-s.cos(10*x)/100
w=s.diff(h,x,2)
assert s.simplify(w-(12*x*x+2+s.cos(10*x)))==0
assert w.subs(x,0)==3
assert s.simplify(w.subs(x,s.pi/10)-(1+3*s.pi**2/25))==0
# pi<4 gives 1+3*pi^2/25 <73/25 <3.
assert Q(73,25)<3
assert s.expand(12*(x-s.Rational(1,6))**2+s.Rational(2,3))==12*x*x-4*x+1
out['strong_tail_obstruction']={'potential':'x^4+x^2-cos(10x)/100','w0':'3','w(pi/10)':'1+3*pi^2/25 <73/25<3','tail':'w(x)>=12x^2+1>4|x|'}
(L/'exact-checks.json').write_text(json.dumps(out,indent=2))
print('Strong-tail exact obstruction PASS')
