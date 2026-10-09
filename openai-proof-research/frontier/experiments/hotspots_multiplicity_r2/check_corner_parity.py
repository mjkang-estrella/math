"""Exact algebra checks for the two-edge corner argument; not a PDE proof."""
from fractions import Fraction as F
from pathlib import Path
import json

# Side signs of the n-th cosine mode are 1 and (-1)^n.
# A derivative of the n=0 radial mode is O(r), so terms involving it
# vanish after multiplication with any n>=1 derivative (nu>1/2).
# For n,m>=1, averaging the two sides kills n+m odd.
# With n+m even >=4, exponent (n+m)*nu-2 is strictly positive.
# Thus (n,m)=(1,1) is the only potentially nonvanishing averaged pair.
checks=[]
for n in range(1,13):
    for m in range(1,13):
        parity_sum=1+(-1)**(n+m)
        inf_exponent=F(n+m,2)-2
        if parity_sum and (n,m)!=(1,1):
            assert inf_exponent>=0
            # nu>1/2 makes even the endpoint equality strict.
        checks.append({'n':n,'m':m,'side_sum_factor':parity_sum,
                       'exponent_inf_at_nu_half':str(inf_exponent)})
# Check the resonant 3*pi/2 angle (nu=2/3): n+m=3 has exponent 0,
# but is killed by the side average. This is the dangerous missed term.
nu=F(2,3)
assert (1+2)*nu-2==0
assert 1+(-1)**(1+2)==0
# Leading derivative polynomial h'=s*a*x + b*y, k'=s*c*x+d*y:
# average sides = a*c*x^2+b*d*y^2; mixed term changes sign.
for a,b,c,d in [(1,2,3,4),(-2,7,0,3),(0,5,-8,1)]:
    x,y=F(7,3),F(11,5)
    average=((a*x+b*y)*(c*x+d*y)+(-a*x+b*y)*(-c*x+d*y))/2
    assert average==a*c*x*x+b*d*y*y
out={'status':'passed','kind':'exact rational/parity checks only',
     'mode_pairs_checked':len(checks),'resonant_nu':'2/3',
     'resonant_mixed_term_cancels':True,
     'only_potential_nonvanishing_averaged_positive_mode_pair':[1,1]}
path=Path(__file__).with_name('results.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
