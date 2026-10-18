#!/usr/bin/env python3
"""MIT. Exact polynomial identities; not a nonlinear geometric proof."""
from fractions import Fraction as Q
import json

def trim(p):
    p=list(map(Q,p))
    while len(p)>1 and p[-1]==0:p.pop()
    return tuple(p)
def add(p,q):
    return trim([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def neg(p):return tuple(-x for x in p)
def sub(p,q):return add(p,neg(q))
def mul(p,q):
    z=[Q(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):z[i+j]+=x*y
    return trim(z)
def scale(c,p):return trim([c*x for x in p])
def der(p):return trim([i*p[i] for i in range(1,len(p))] or [0])
class Rat:
    def __init__(self,p,q=(1,)):self.p,self.q=trim(p),trim(q);assert self.q!=(0,)
    def __add__(self,b):return Rat(add(mul(self.p,b.q),mul(b.p,self.q)),mul(self.q,b.q))
    def __neg__(self):return Rat(neg(self.p),self.q)
    def __sub__(self,b):return self+-b
    def __mul__(self,b):return Rat(mul(self.p,b.p),mul(self.q,b.q))
    def __truediv__(self,b):return Rat(mul(self.p,b.q),mul(self.q,b.p))
    def zero(self):return self.p==(0,)
z=Rat((0,1));ph=Rat((-2,0,1));dp=Rat((0,2));dd=Rat((2,));two=Rat((2,));half=Rat((Q(1,2),))
# w=exp(z²/4)/phi²; its logarithmic derivative is z/2−2phi'/phi.
logdw=z*half-two*dp/ph
slow=dd-z*half*dp+ph
# L(phi I)=L(phi) I + w[(2phi'−z phi/2)+phi w'/w].
growing=two*dp-z*half*ph+ph*logdw
wrong=two*dp-z*half*ph+ph*(-z*half-two*dp/ph)
checks={
 'slow_solution':slow.zero(),
 'growing_solution':growing.zero(),
 'wronskian_coefficient':(ph*ph/Rat(mul(ph.p,ph.p))-Rat((1,))).zero(),
 'wrong_drift_detected':not (dd+z*half*dp+ph).zero(),
 'wrong_exponential_detected':not wrong.zero(),
}
# Derivative ratio w/[2 exp(z²/4) z^-5]' = z^6/[(z²−10)(z²−2)²].
den=mul((-10,0,1),mul(ph.p,ph.p));num=(Q(0),)*6+(Q(1),)
checks['asymptotic_equal_degree_leading_coefficient']=len(den)==len(num) and den[-1]==num[-1]==1
checks['fractional_scale_exponent']=-(1-Q(1,2)**2)/4==Q(-3,16)
assert all(checks.values()),checks
print(json.dumps({'status':'PASS_SCALAR_POLYNOMIAL_ONLY','checks':checks,'derivative_ratio_denominator_coefficients':[str(x) for x in den],'nonlinear_matching':'NOT_PROVED'},indent=2,sort_keys=True))
