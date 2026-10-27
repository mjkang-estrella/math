#!/usr/bin/env python3
"""Independent symbolic arithmetic for the proposed fixed Smale witness.

Connected branch completeness is proved in Lean, not by finite sampling here.
"""
from fractions import Fraction
from pathlib import Path
import json
import sympy as s

y, q, w = s.symbols('y q w', real=True)
root = s.sqrt(3) * q
poly = w * (w - root) * (w + root)
deleted = (w - root) * (w + root) + w * (w + root) + w * (w - root)
checks = {
    'literal_product_is_cubic': s.expand(poly - (w**3 - 3*q*q*w)) == 0,
    'deleted_is_derivative': s.expand(s.diff(poly, w) - deleted) == 0,
    'derivative_fully_split': s.expand(deleted - 3*(w-q)*(w+q)) == 0,
    'plus_critical': s.expand(deleted.subs(w, q)) == 0,
    'minus_critical': s.expand(deleted.subs(w, -q)) == 0,
    'test_derivative_constant': s.expand(deleted.subs(w, y)).subs(q*q, y*y+s.Rational(1,16)) == -s.Rational(3,16),
}
qend = s.sqrt(17) / 4
endpoint = s.simplify(poly.subs({w:-1, q:qend}) - poly.subs({w:qend, q:qend}))
checks['endpoint_exact'] = s.simplify(endpoint - (s.Rational(35,16) + 2*qend**3)) == 0
checks['endpoint_exceeds_four'] = bool(endpoint > 4)
checks['derivative_times_distance_bound'] = Fraction(3,16)*Fraction(9,4) == Fraction(27,64)
checks['formal_weaker_gap_suffices'] = Fraction(27,64) < 2
checks['inverse_constant'] = Fraction(-3,16)*Fraction(-16,3) == 1
checks['branch_upper_bound_squared'] = Fraction(17,16) < Fraction(5,4)**2
assert all(checks.values()), checks
out = {'status':'PASS: exact algebra and rational bounds; topology is Lean-proved',
       'checks':checks, 'count':len(checks),
       'endpoint_value_gap_exact':str(endpoint),
       'endpoint_value_gap_decimal':str(s.N(endpoint,60)),
       'formal_scope_note':'Lean needs only value gap >2; the stronger >4 remains an independently checked algebraic fact.',
       'discovery_credit':0}
Path(__file__).with_name('certificate-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
