import pathlib,json,math,itertools
from fractions import Fraction as F
P=pathlib.Path(__file__).resolve().parent
# Eq13 with all four x_i=1. Exact inclusion-exclusion moments, not proof of novelty.
m=4
T=lambda r:F(sum((-1)**(m-j)*math.comb(m,j)*j**(m+r) for j in range(m+1))*math.factorial(r),math.factorial(m+r))
a=[]
for r in [1,3,5,7]:
 lhs=T(r)/T(1)**r;rhs=sum((-1)**(k+1)*math.comb(r,k)*T(r-k)/T(1)**(r-k) for k in range(1,r+1));assert lhs==rhs;a.append({'m':m,'x':[1]*m,'odd_degree':r,'lhs':str(lhs),'rhs':str(rhs)})
# Cartesian P2 square P2 has four edges and degree2; hence C4 and not K4.
edges=[(u,v) for u,v in itertools.combinations(list(itertools.product(range(2),repeat=2)),2) if sum(x!=y for x,y in zip(u,v))==1]
assert len(edges)==4
(P/'calculation-results.json').write_text(json.dumps({'executed':True,'recurrence_exact_instances':a,'cartesian_P2_P2_edges':edges,'strong_P2_P2_edges':6,'limit':'No general new theorem, no Korselt enumeration, no strong-product conjecture resolution'},indent=2)+'\n')
print((P/'calculation-results.json').read_text())
