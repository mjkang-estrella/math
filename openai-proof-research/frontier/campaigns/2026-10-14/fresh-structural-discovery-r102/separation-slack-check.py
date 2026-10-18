#!/usr/bin/env python3
"""Exact checks of NEW retained margins using stipulated source case bounds."""
from fractions import Fraction as F
import json
eta=F(1,1000); c=1-eta
def theta(m,t):
 y=t*t
 return (1+m)/4*(1+y/30+y*y/1680)/(1+y/36)
checks=[]
def check(name,lhs,rhs):
 assert lhs<rhs,name
 checks.append({'name':name,'margin':str(rhs-lhs)})
check('R1',F('.3425'),c*theta(F('.38'),F(0)))
check('U1_V1',F('.31'),c*theta(F('.68'),F(0)))
check('T1',F('.39'),c*theta(F('.68'),F(0)))
check('P1_low',F('.20'),c*theta(F('.19'),F(0)))
check('P1_cross_to4',F('.284143'),c*theta(F('.19'),F(0)))
check('P1_4to5',F('.345394'),c*theta(F('.19'),F(4)))
check('P1_from5',F('.38105'),c*theta(F('.19'),F(5)))
check('O_low_to4',F('.20'),c*F('.25'))
check('O_low_upper_constant',F('.20'),c*F('.25'))
check('O_cross_upper_notT',F('.23'),c*F('.25'))
check('O_cross_upper_T',F('.39'),c*theta(F(0),F('6.5')))
for name,a,b,d in [('O_low_quadratic',c*F('.00260'),-F('.011'),c*F('.25')-F('.144')),('O_cross_quadratic',c*F('.00260'),-F('.031'),c*F('.25')-F('.156'))]:
 assert a>0 and d>0
 check(name+'_negative_discriminant',b*b,4*a*d)
# Reason-checked controls: an overlarge retained fraction fails an actual source bound.
assert not F('.3425')<(1-F(1,100))*theta(F('.38'),F(0))
# Polynomial identity for H1 coefficient (degrees>=2), exact coefficients.
assert (19,1322,-2720)==(19,1360-38,-2720)
print(json.dumps({'status':'PASS','eta':str(eta),'exact_comparisons':checks,'negative_control':'eta=1/100 fails R1 bound as expected','scope':'Checks derived rational margins, not upstream interval certificates or full theorem proof.'},indent=2))
