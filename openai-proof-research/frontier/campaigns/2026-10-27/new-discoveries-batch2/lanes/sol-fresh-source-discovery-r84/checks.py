from fractions import Fraction as F
from math import comb,factorial
from pathlib import Path
import json
P=Path(__file__).resolve().parent
rows=[]
for d in range(2,81):
 N=2**d-d-1
 D=sum(-F(4*(comb(d,k)-1)*(2*k-d)**2,d*d) for k in range(d+1))
 B=sum(F(4*(comb(d,k)-1)*((2*k-d)**2-d),d*(d-1))-F(4*(comb(d,k)-1)*(2*k-d)**2,d*d) for k in range(d+1))
 assert D-B==F(4*(d+1),3)
 assert D+(d-1)*B==-4*N
 A=sum(k*(comb(d,k)-1) for k in range(d+1));assert A==F(d*N,2)
 rows.append(dict(d=d,contrast_eigenvalue=str(D-B),diagonal_eigenvalue=str(D+(d-1)*B),binomial_exponent=A))
# Full d=2 finite witness. The fiber-volume factor is p1, up to constant sqrt(2).
p1=lambda a,b:a+b-2*a*b
assert p1(F(1,4),F(3,4))==F(5,8)
assert p1(F(3,4),F(1,4))==F(5,8)
assert p1(F(1,2),F(1,2))==F(1,2)<F(5,8)
# d=3 diagonal profile has A=6, second derivative / (A*[t(1-t)]^(A-2))
# is (A-1)*(1-2t)^2-2*t*(1-t).
t=F(1,10);A=6;bracket=(A-1)*(1-2*t)**2-2*t*(1-t)
assert bracket==F(151,50)>0
out={'status':'PASS','exact_only':True,'dimensions_checked':len(rows),'d2_midpoint':{'endpoint':'5/8','midpoint':'1/2'},'d3_diagonal_second_derivative_positive_bracket':str(bracket),'eigenvalue_checks':rows,'scope':'Finite checks validate identities; proof for all d is in discovery.md. Uncredited routine source correction.'}
(P/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='eigenvalue_checks'},indent=2))
