from fractions import Fraction as F
from pathlib import Path
import json
p=Path(__file__).parent
rows=[]
for n,lo,hi in [(1,13,16),(2,48,51),(3,102,105)]:
 L=F(49,5)*(F(n)+F(1,4))**2-F(3,4)-F(1,3*n)
 U=10*(F(n)+F(1,4))**2-F(3,4)+F(1,3*n)
 assert lo<L and U<hi
 rows.append({'n':n,'lower':str(L),'upper':str(U),'enclosure':[lo,hi]})
assert F(1)-F(9,8)+F(81,192)-F(729,9216)==F(2007,9216)
assert 32**2-16*57==112
assert 4*3**4-32*4-F(4,27)>0
# Formal polynomials: L_m = pi^2*(2m-1/2); determinant cancels m^2 and m.
a,b=F(2),F(-1,2)
assert a*a==4
# independent expanded coefficients of (am+b)^2 - (am+b-a)(am+b+a)
assert [b*b-(b-a)*(b+a),2*a*b-a*(b-a)-a*(b+a),a*a-a*a]==[F(4),0,0]
(p/'exact-diagnostic.json').write_text(json.dumps({'rational_enclosures':rows,'first_determinant_lower_bound':112,'uniform_determinant_lower_bound':str(4*3**4-32*4-F(4,27)),'P9':'2007/9216','all_checks_pass':True,'role':'Exact algebra validation; the analytic phase proof in 326635-proof.md supplies the all-index argument. No numerical zero scan.'},indent=2))
print('Exact algebra checks pass')
