from fractions import Fraction as F
from pathlib import Path
import json
# Unit interval indicator convolves to x on [0,1], 2-x on [1,2].
a=F(1,2);b=2*(2-1)-(F(4,2)-F(1,2));assert a==b==F(1,2)
# Exact rational sign sequence finite generating-polynomial product identity.
x=F(7,8);n=8
s=sum((-1)**i.bit_count()*x**i for i in range(2**n));p=F(1)
for j in range(n):p*=1-x**(2**j)
assert s==p
(Path(__file__).parent/'bounded-checks.json').write_text(json.dumps({'executed':True,'unit_box_convolution_projection_coefficients':['1/2','1/2'],'finite_Thue_Morse_identity':{'terms':256,'x':'7/8','exact_match':True},'limits':'Illustrative classical identities only. No infinite optimality, fast hp complexity or target proof follows. No target search sweeps.'},indent=2)+'\n')
