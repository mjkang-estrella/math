# Closed forms (in m) of low coefficients r_{0,F} for 342364, by exact interpolation over m of a fixed
# residue class m = q*t + s, expressed in the binomial basis binom(t,i); verified on extra points.
import sys, json
from fractions import Fraction
sys.path.insert(0, __import__('os').path.dirname(__file__))
from tcheb import T, add, v2
from reduced import divyy
def r0(m):
    A1=T([1],m); A2=T(A1,m); return divyy(add(A2,[1],-1))
def newton(vals):
    # forward differences -> coefficients b_i with P(t)=sum b_i binom(t,i)
    b=[]; cur=list(vals)
    while cur:
        b.append(cur[0]); cur=[cur[i+1]-cur[i] for i in range(len(cur)-1)]
    return b
q,s,F,npts,nver=map(int,sys.argv[1:6])
ms=[q*t+s for t in range(npts+nver)]
vals=[]
for mm in ms:
    r=r0(mm); vals.append(r[F] if F<len(r) else 0)
b=newton(vals[:npts])
# degree check: trailing differences zero
deg=max(i for i,x in enumerate(b) if x!=0)
from math import comb
pred=[sum(b[i]*comb(t,i) for i in range(len(b))) for t in range(npts+nver)]
ok=pred==vals
print(json.dumps(dict(cls=f'm={q}t+{s}',F=F,degree_in_t=deg,binomial_basis_coeffs=b[:deg+1],min_nu2_coeff=min(v2(x) for x in b[:deg+1] if x),verified_points=len(ms),verified=ok,first_vals_nu2=[v2(v) for v in vals[:12]])))
