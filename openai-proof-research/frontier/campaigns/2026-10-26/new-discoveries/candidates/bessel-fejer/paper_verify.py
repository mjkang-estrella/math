#!/usr/bin/env python3
"""Exact recalculation of every finite bound displayed in the manuscript."""
from fractions import Fraction as F
from math import factorial,comb
from pathlib import Path
import json
p=[F((-1)**r,factorial(r)**2) for r in range(20)]
h=[F((-1)**r,factorial(r)*factorial(r+1)) for r in range(20)]
def bernstein(coeff,a,b):
 # Two explicit binomial changes of basis over the rationals.
 shifted=[sum(coeff[r]*comb(r,k)*a**(r-k)*(b-a)**k for r in range(k,20)) for k in range(20)]
 return [sum(shifted[k]*F(comb(i,k),comb(19,k)) for k in range(i+1)) for i in range(20)]
l1,u1,l2,u2=map(F,['2.4048','2.4049','5.5200','5.5201']);c=F(47,50)
rows=[('H0',h,F(0),F(9,4),F(1,5),'lower'),('Jmiddle',p,F(9,4),l2*l2/4,-F(1,50000),'upper'),('Hsecond',h,l2*l2/4,u2*u2/4,-F(3,25),'upper'),('JfirstScaled',p,(c*l1)**2/4,(c*u1)**2/4,F(3081,40000),'upper'),('JsecondScaled',p,(c*l2)**2/4,(c*u2)**2/4,-F(11381,100000),'upper')]
checks=[]
for name,co,a,b,bound,direction in rows:
 bs=bernstein(co,a,b)
 assert (min(bs)>=bound if direction=='lower' else max(bs)<=bound)
 checks.append({'name':name,'interval':[str(a),str(b)],'bound':str(bound),'direction':direction,'result':'PASS'})
e=2*F(9)**20/factorial(20)**2;eh=2*F(9)**20/(factorial(20)*factorial(21))
assert e<F(1,10**17) and eh<F(1,10**18)
assert F('1.4204')**5<l1*l1 and u1*u1<F('1.4205')**5
assert F('1.9805')**5<l2*l2 and u2*u2<F('1.9806')**5
assert F(3081,40000)+e<F(7703,100000)
assert -F(11381,100000)+e<-F(569,5000)
upper=F(2,3)*F(14205,10000)*F(7703,100000)-F(1,3)*F(19805,10000)*F(569,5000)
assert upper==-F(653867,300000000) and upper<-F(1,500)
out={'status':'PASS exact rational manuscript calculation','rows':checks,'tail_bounds':[str(e),str(eh)],'final_upper_bound':str(upper),'upper_bound_less_than_minus_one_over_500':True,'not_a_substitute_for_formal_or_independent_review':True}
Path(__file__).with_name('paper-math-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS five whole-interval rows, tails, fifth-power bounds and final fraction')
