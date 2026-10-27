#!/usr/bin/env python3
"""Exact arithmetic for the proposed witness; numerical section is evidence only."""
from fractions import Fraction as F
import json
from pathlib import Path
import sympy as s
import mpmath as mp

x0, a0 = F(1, 50), F(527, 1000)
P = x0**4 + a0*x0**2 + F(7,40)*a0-F(31,336)
P1, P2 = 4*x0**3+2*a0*x0, 12*x0**2+2*a0
assert (P,P1,P2)==(F(91379,525000000),F(2639,125000),F(2647,2500))
gap=F(155,294)-a0
assert gap==F(31,147000)>0
log2upper=F(56,81)+F(1,540)
log5lower=2*(F(2,3)+F(2,3)**3/3+F(2,3)**5/5)
assert log2upper==F(1123,1620)<F(7,10)
assert log5lower==F(1924,1215)
assert F(2,3)+2*log5lower==F(4658,1215)>F(15,4)
lower=24*P2*(F(15,4)-F(31,15))-48*P1/x0+24*P*(1/x0**2-20)-2
assert lower==F(510221,1093750)>0
x,a=s.symbols('x a', positive=True)
h=s.Function('h')
g=24*(x**4+a*x*x)*(h(x)-s.log(x))-x*x+s.Rational(7,40)-a
g2=24*((12*x*x+2*a)*h(x)+(8*x**3+4*a*x)*s.diff(h(x),x)+(x**4+a*x*x)*s.diff(h(x),x,2)-(12*x*x+2*a)*s.log(x)-7*x*x-3*a)-2
assert s.simplify(s.diff(g,x,2)-g2)==0
mp.mp.dps=70
am=mp.mpf(527)/1000
G=lambda t:24*(t**4+am*t*t+mp.mpf(7)*am/40-mp.mpf(31)/336)*(mp.digamma(t+mp.mpf('0.5'))-mp.log(t))-t*t+mp.mpf(7)/40-am
v=mp.diff(G,mp.mpf(1)/50,2)
assert v>mp.mpf(lower.numerator)/lower.denominator
out={'status':'PASS: exact arithmetic and symbolic identity; analytic estimates proved in PROOF.md',
     'a':str(a0),'x':str(x0),'parameter_gap':str(gap),'P':str(P),'P1':str(P1),'P2':str(P2),
     'Gsecond_strict_lower_bound':str(lower),'Gsecond_numerical_evidence_only':mp.nstr(v,60),
     'formal_endpoint':'absent','discovery_credit':0}
Path(__file__).with_name('certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
