"""Finite normalization checks only; invoked after immutable replay, never ancestors."""
from fractions import Fraction as F
from math import gamma,pi,sqrt

def checks():
 count=0
 # The inverse orbit metric, including the factor two in its eigen-directions.
 for x in range(2,13):
  for y in range(1,x):
   u=x*x+y*y;v=-2*x*y;det=u*u-v*v
   assert det==(x*x-y*y)**2
   for p,q in [(1,0),(0,1),(1,1),(1,-1),(2,-3)]:
    inverse=F(u*(p*p+q*q)-2*v*p*q,det)
    split=F((p+q)**2,2*(x-y)**2)+F((p-q)**2,2*(x+y)**2)
    assert inverse==split;count+=1
 assert 3*6+3*2==24 and 27-24==3
 assert F(3,2)+F(3,4)==F(9,4)
 assert 384**2*6<1024**2
 assert F(3072+9,3)-1024==3
 assert 2*1540>3072+6
 assert (2*1540+6,2*1540,0,0)==(3086,3080,0,0)
 assert F(64,384*45)==F(1,270)
 # Independent unsimplified momentum-ball/beta prefactor versus final expression.
 raw=(2*pi)**-3*(4*pi/3)*2**1.5*gamma(.25)**3*gamma(2.5)/(96*gamma(3.25))
 final=sqrt(2)*gamma(.25)**2/(270*pi**1.5)
 assert abs(raw/final-1)<1e-13
 return dict(status='PASS',metric_inverse_samples=count,normalization_budget=True,
             chamber_prefactor=final,scope='Finite arithmetic only; no proof of domain reduction, Poincare theorem, Weyl limit, novelty, or acceptance.')
