from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
P=Path(__file__).resolve().parent
# Rational projective-circle gap partitions and exact Jensen inequality.
nchecks=0
for n in range(1,6):
 for ds in product(range(7),repeat=n):
  if sum(ds)!=6:continue
  gaps=[F(d,6) for d in ds]
  for a in [F(j,24) for j in range(13)]:
   lhs=sum(max(d-2*a,0) for d in gaps)
   rhs=max(1-2*n*a,0)
   assert lhs>=rhs;nchecks+=1
# Exact polynomial coefficient in F'' along I+s(C-I), C_ij=-1/2 for i!=j.
# q=P(|Z|>=t), c=E[(Z²-1)1{|Z|>=t}]. Coefficients q³,q²c,qc².
trA2=F(3,2);pairs=F(3,4)
pol=[trA2/2-trA2+pairs,-trA2+2*pairs,pairs]
assert pol==[0,0,F(3,4)]
# det(I+sA)=(1-s)(1+s/2)^2=1-3s²/4-s³/4.
det=[F(1),F(0),-F(3,4),-F(1,4)]
for s in [F(j,12) for j in range(13)]:
 assert sum(det[k]*s**k for k in range(4))==(1-s)*(1+s/2)**2
# Gaussian-cosine small-t coefficient difference positive: 2-sqrt3>0.
assert 3<2**2
out={'status':'PASS','arc_gap_checks':nchecks,'second_variation_coefficients_q3_q2c_qc2':list(map(str,pol)),'determinant_coefficients':list(map(str,det)),'interpretation':'Exact route/parameter diagnostics only; neither source conjecture resolved.'}
(P/'check-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
