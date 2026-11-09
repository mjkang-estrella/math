"""Independent exact signs using a closed finite-difference coefficient formula.
No imports from author experiments or formal certificate data.
"""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import hashlib,json,sys
sys.set_int_max_str_digits(0)
K=48
lo,hi=Q(61,1000),Q(613,10000)
# Chain rule coefficient from [z^t]((1+z)^k-1)^j/j!:
# (k-1)! C(k,t,j) = t!/j! sum_a (-1)^(j-a) C(j,a) C(ka,t).
def c_closed(k,t,j):
 return Q(factorial(t),factorial(k-1)*factorial(j))*sum((-1)**(j-a)*comb(j,a)*comb(k*a,t) for a in range(j+1))
def data(k):return [c_closed(k,k+1,j+2) for j in range(k)]
def eval_source(k,x):
 y=x**k;g=(1-y);geom=(1-y)/(1-x)
 # Direct original Cor3.7 sums; writing x^k-1=-g is purely exact arithmetic.
 rho=sum((-1)**j*factorial(j)*c*( (-g)**(k-j-1)*y**(j+1)-(-g)**k) for j,c in enumerate(data(k)))
 sigma=sum((-1)**j*comb(k+1,j+2)*(x**(j+1)*(x-1)**(k-j-1)*geom**k-(-g)**k) for j in range(k))
 return rho,sigma
# Independent small-table normalization checks against the actual published table.
for x in [Q(0),Q(1,3),Q(2,3)]:
 r,s=eval_source(2,x)
 assert r==-4*(1+x*x)
 assert s==-2-3*x+x**3
 r,s=eval_source(3,x)
 assert r==9+63*x**3+9*x**6
 assert s==3+6*x+10*x*x+6*x**3+3*x**4-2*x**5+x**8
assert lo*(1+lo)**47<1<hi*(1+hi)**47
rows=[]
for x,sgn in [(Q(1,100),-1),(Q(1,10),1),(Q(1,2),-1),(Q(3,5),1),(Q(4,5),-1)]:
 r,s=eval_source(K,x)
 p_lo,p_hi=lo*r-s,hi*r-s
 assert sgn*p_lo>0 and sgn*p_hi>0
 # Entire alpha interval follows because p(alpha) is affine.
 rows.append({'x':str(x),'sign':sgn,'rho_negative':r<0,'sigma_over_rho':str(s/r),'lo_numerator':str(p_lo.numerator),'lo_denominator':str(p_lo.denominator),'hi_numerator':str(p_hi.numerator),'hi_denominator':str(p_hi.denominator)})
 print(str(x),sgn,'rho_sign',-1 if r<0 else 1,'sigma/rho',float(s/r),flush=True)
out={'method':'closed coefficient formula from binomial finite differences; original Cor3.7 finite sums; no author code/data imported','k':K,'alpha_bounds':[str(lo),str(hi)],'alpha_equation':'alpha*(1+alpha)^47=1','small_source_table_checks':'k2 and k3, x0/1over3/2over3 PASS','rows':rows}
p=Path(__file__).resolve().parent/'independent-sign-certificate.json';p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS',hashlib.sha256(p.read_bytes()).hexdigest())
