from pathlib import Path
from fractions import Fraction as F
from math import factorial
import sympy as s
import json

p=Path(__file__).resolve().parent
x,t=s.symbols('x t',positive=True)
M=s.Rational(100,9)*(x+3)**2/((x+1)*(x+10)**2)
partial=s.Rational(100,729)*(4/(x+1)+77/(x+10)-441/(x+10)**2)
assert s.factor(M-partial)==0 and M.subs(x,0)==1
rho=s.Rational(100,729)*(4*s.exp(-t)+(77-441*t)*s.exp(-10*t))
assert s.simplify(s.integrate(rho,(t,0,s.oo)))==1
assert s.factor(s.integrate(s.exp(-x*t)*rho,(t,0,s.oo))-M)==0
v=F(18,7);lower=sum((v**j/F(factorial(j)) for j in range(8)),F())
assert lower>F(49,4)
z=F(4,5);spectral=z+2*z**10-2*z**3;assert spectral==F(-90348,9765625)
# k=35 is the exponent in the34th derivative of -(log M)'.
k=35;xx=157
negative=F(1,(xx+1)**k)+F(2,(xx+10)**k)-F(2,(xx+3)**k)
assert negative<0
Q=(xx+3)**k*(xx+10)**k+2*(xx+1)**k*(xx+3)**k-2*(xx+1)**k*(xx+10)**k
assert Q<0
# Positive Gamma parameters, in normalized Pochhammer notation.
A=[1,4,4,10,10];C=[2,3,3,11,11]
rational=s.prod((x+3)/3 for _ in range(2))*s.prod(10/(x+10) for _ in range(2))/(x+1)
assert s.factor(rational-M)==0
oldnum=200*x**3+1353*x**2+2615*x+1468
# Exact Sturm counts for the three real negative zeros in Dufresne's example.
intervals=[(F(-4),F(-3)),(F(-2),F(-3,2)),(F(-11,10),F(-1))]
counts=[int(s.Poly(oldnum,x).count_roots(s.Rational(a.numerator,a.denominator),s.Rational(b.numerator,b.denominator))) for a,b in intervals]
assert counts==[1,1,1]
out={'credit':0,'disposition':'EXCLUDED already public source-question refutation, Dufresne2010 Example2 and Wang2024 section2.2',
     'own_witness':{'A':A,'C':C,'M':str(M),'density':str(rho),'normalization':1,'laplace_identity':'exact',
        'density_positivity':'4exp(u)+77-49u >=126-49log(49/4)>0; exp(18/7)>49/4 by rational Taylor lower bound',
        'exp_taylor7_lower':str(lower),'negative_spectral_at_exp_minus_t_4_over_5':str(spectral),
        'log_derivative_failure_order':35,'log_derivative_failure_point':xx,'negative_power_sum':str(negative),'integer_numerator_sign_certificate':str(Q)},
     'dufresne_positive_real_parameters':{'cubic':str(oldnum),'isolating_intervals_for_negative_zeros':[[str(a),str(b)]for a,b in intervals],'exact_sturm_counts':counts},
     'warning':'The cubic in Dufresne/Wang is an auxiliary rational factor. It is NOT silently identified with the final Gamma-quotient Mellin transform.'}
(p/'exact-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS density/Laplace/Gamma bridge/log sign/old-real-roots; excludedcredit0.')
