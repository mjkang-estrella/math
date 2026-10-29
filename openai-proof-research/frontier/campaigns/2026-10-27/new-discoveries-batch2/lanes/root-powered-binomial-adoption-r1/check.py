import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[name]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
from math import comb
from fractions import Fraction as F
from itertools import accumulate
from pathlib import Path
import json

def C(n,i): return comb(n,i) if 0<=i<=n else 0
def D(r,l,a):return sum((C(r,i)*a**i)**l for i in range(r+1))
def bases(r,j):
    p=[(r+2)*C(r,i)*C(r+2,j-i) for i in range(r+3)]
    p += [(r+1)*C(r,i)*C(r+1,j-i) for i in range(r+3)]
    n=[(r+2)*C(r,i)*C(r+1,j-i) for i in range(r+3)]
    n += [(r+1)*C(r+1,i)*C(r+1,j-i) for i in range(r+3)]
    return sorted(p,reverse=True),sorted(n,reverse=True)

identity_checks=0
for r in range(12):
    for l in (1,2,3,5,8):
        for a in (F(1,10),F(1,2),F(1),F(3)):
            b,c,d=[D(t,l,a) for t in (r,r+1,r+2)]
            E=(r+2)**l*b*d-((r+2)**l-(r+1)**l)*b*c-(r+1)**l*c*c
            difference=(r+2)**l*(d/c-1)-(r+1)**l*(c/b-1)
            assert E==b*c*difference
            expanded=sum((sum(t**l for t in bases(r,j)[0])-sum(t**l for t in bases(r,j)[1]))*a**(l*j) for j in range(2*r+3))
            assert E==expanded
            identity_checks+=1
assert (2*4)*(3*(F(8,4)-1)-2*(F(4,2)-1))==8
assert 3*2*8-(3+2)*2*4+2*4**2==40

coefficient_checks=0
for r in range(21):
    for j in range(2*r+3):
        p,n=bases(r,j)
        assert sum(p)-sum(n)==C(2*r+1,j-1)
        for l in range(1,41):
            assert sum(t**l for t in p)>=sum(t**l for t in n)
            coefficient_checks+=1

p,n=bases(4,2)
assert sum(p[:2])==244 and sum(n[:2])==245
squared_checks=0
for r in range(61):
    for j in range(2*r+3):
        p,n=bases(r,j)
        assert all(a>=b for a,b in zip(accumulate(t*t for t in p),accumulate(t*t for t in n)))
        squared_checks+=1
out={'status':'PASS','cleared_difference_identity_checks':identity_checks,
     'coefficient_checks':coefficient_checks,'squared_majorization_cases':squared_checks,
     'failed_unsquared_majorization':{'r':4,'j':2,'positive_bases':bases(4,2)[0],
       'negative_bases':bases(4,2)[1],'top_two_sums':[244,245]},
     'scope':'Finite exact diagnostics; all-order squared-majorization, A-monotonicity and source conjecture UNPROVED.'}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
