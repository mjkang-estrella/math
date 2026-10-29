from fractions import Fraction as Q
import json,pathlib
N=100
assert 2000*25**N<27**N
L=2*(Q(9323,12)-Q(7725,32000))-(Q(115,3)+Q(75,8000))**2
assert L>80
num=2*875**35-825**35-891**35
assert num<0
out={'2000_times_25power100':2000*25**100,'27power100':27**100,'curvature_rational_lower_factor':str(L),'greater_than':80,'N35_delta1_numerator':num,'N35_delta1_denominator':2475**35}
pathlib.Path('compact.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
