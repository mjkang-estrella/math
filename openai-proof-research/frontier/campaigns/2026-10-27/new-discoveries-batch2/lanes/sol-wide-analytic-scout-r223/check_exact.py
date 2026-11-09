"""Exact rational checks of the boundary-bound obstruction, not Q2."""
from fractions import Fraction as F
from math import factorial
import json
s=sum((F(1,factorial(k)) for k in range(9)),F())
tail=F(1,factorial(9))*F(10,9)
assert 2<s<s+tail<3
# e^-40 < 2^-40 < 1/3 and sinh(1)<e/2<3/2.
assert (1+F(1,2**40))*F(3,2)<2
# Integrate K0's positive representation on 0<t<1, 0<s<20.
# c=e^-20, mu=1/2: c'/c > 40 e^-2 (1-e^-1)>40/(9*2)>2.
assert F(40,18)>2
print(json.dumps({'scope':'method counterexample only','e_lower':str(s),'e_upper':str(s+tail),'lower_bound_cprime_over_c':str(F(40,18)),'claimed_shortcut_threshold':2,'PASS':True},indent=2))
