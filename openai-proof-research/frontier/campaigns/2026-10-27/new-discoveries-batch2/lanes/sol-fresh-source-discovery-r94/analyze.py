from pathlib import Path
import sympy as s,json
p=Path(__file__).parent;x,a,q,t,y=s.symbols('x a q t y',real=True)
H4=s.hermite_prob(4,x);H8=s.hermite_prob(8,x);r=1+a*H4
N=s.expand(-r*r+s.diff(r,x,2)*r-s.diff(r,x)**2)
P=s.Poly(N,x); print('logconcavity numerator',s.factor(N));print('a=1/100',s.factor(N.subs(a,s.Rational(1,100))))
# Sufficient global control: r>=1-6a; r''<=12a*x²; r>=a*(x²-3)²+1-6a.
# r''/r <=12a*x²/r. Thus log f''<=-1+12a*y/r.
D=s.expand(r-12*a*x*x);print('r-12ay',s.factor(D));print('minimum in y',s.simplify(D.subs(x*x,9)))
# r-12ay= a(y-9)^2+1-78a, so a<=1/156 gives strong curvature <= -1/2 using r-24ay instead.
print('r-24ay',s.expand(r-24*a*x*x));print('minimum',1-222*a)
R=1+a*q*q*(t*t+(1-t)**2)*H4+a*a*q**4*t*t*(1-t)**2*H8
print('midpoint r',s.expand(R.subs(t,s.Rational(1,2))));print('midpoint r2',s.factor(s.diff(R,t,2).subs(t,s.Rational(1,2))))
# Gaussian Hermite orthogonality gives second-order entropy coefficient.
A=t*t+(1-t)**2; c=s.expand(-s.factorial(4)*a*a*q**4*A*A/2)
curv=s.factor(s.diff(c,t,2));print('leading curvature',curv)
(p/'analysis.json').write_text(json.dumps({'logconcavity_numerator':str(N),'r_minus_12ay':str(s.expand(r-12*a*x*x)),'r_minus_24ay':str(s.expand(r-24*a*x*x)),'leading_entropy_curvature':str(curv),'midpoint_second_derivative_density_ratio':str(s.factor(s.diff(R,t,2).subs(t,s.Rational(1,2))))},indent=2))
