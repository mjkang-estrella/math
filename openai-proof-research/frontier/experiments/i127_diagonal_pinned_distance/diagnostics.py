"""Finite exact instances only. No universal analytic or substantiality certification."""
from fractions import Fraction as F
from itertools import product

def check():
 count=0
 # Exact conditional expectation and sign averaging for rational scalar Hilbert coordinates.
 weights=[F(1,10),F(2,10),F(3,10),F(4,10)]
 vals=[(F(2),F(-1)),(F(-3),F(4)),(F(5),F(2)),(F(-1),F(-2))]
 cells=[[0,1],[2],[3]]
 sums=[tuple(sum(weights[i]*vals[i][j] for i in c) for j in range(2)) for c in cells]
 qs=[sum(weights[i] for i in c) for c in cells]
 norm=lambda v:sum(x*x for x in v)
 signs=list(product([-1,1],repeat=3))
 assert sum(norm(tuple(sum(s[k]*sums[k][j] for k in range(3)) for j in range(2))) for s in signs)/len(signs)==sum(map(norm,sums));count+=1
 full=sum(weights[i]*norm(vals[i]) for i in range(4))
 projected=sum(norm(v)/q for v,q in zip(sums,qs))
 residual=sum(weights[i]*norm(tuple(vals[i][j]-sums[k][j]/qs[k] for j in range(2))) for k,c in enumerate(cells) for i in c)
 assert full==projected+residual;count+=1
 mean=tuple(sum(weights[i]*vals[i][j] for i in range(4)) for j in range(2))
 variance=sum(weights[i]*weights[k]*norm(tuple(vals[i][j]-vals[k][j] for j in range(2))) for i in range(4) for k in range(4))/2
 assert full==norm(mean)+variance;count+=1
 # Enumerated branching schedules: all-prefix Frostman exponent and frozen identity.
 branches=0
 for s in [F(6,5),F(3,2),F(7,4)]:
  a=0;m=0
  for j in range(1,5):
   b=max(a+4,j*j*a+j*j+8)
   for n in range(a+1,b+1):
    m+=2;assert m>=s*n;branches+=1
   a2=(m*s.denominator)//s.numerator
   for n in range(b+1,a2+1):assert m>=s*n;branches+=1
   assert 0<=m-s*a2<s
   L=a2-b
   if L>=2:
    # Truncated profile cost of a frozen interval is geometric, not a constant.
    k=min(L-1,12)
    assert sum(2**l for l in range(k+1))==2**(k+1)-1;count+=1
    N=a2
    assert 2*a2>N+b # forbidden curvature jump at N=a2
    assert 2*a2<=(b+2*L)+b # exact permissible frequency threshold
    count+=2
   a=a2
 # Exact GLW closure inequalities and witness gap.
 exponents=0
 for alpha in [F(11,10),F(5,4),F(3,2),F(7,4)]:
  for beta in [F(7,4),F(2)]:
   if alpha>beta:continue
   d1=(beta-alpha)/(2*beta-1)
   d2=(beta-alpha)/((alpha+1)*(2*beta-alpha-1))
   polynomial=alpha**3-(2*beta-1)*alpha**2-2*alpha+3*beta-1
   assert (max(d1,d2)<alpha-1)==(alpha>F(3,2)-1/(2*beta) and polynomial<0);exponents+=1
 assert max(F(9,10)/3,F(9,10)/(F(21,10)*F(19,10)))==F(3,10)
 # Finite Cantor probability mass and dilation support checks, no Fourier asymptotic inference.
 lam=F(1,4);zs=[F(0)]
 for n in range(1,7):
  zs=[lam*z+c for z in zs for c in [F(0),1-lam]]
  assert len(set(zs))==2**n and all(0<=z<=1 for z in zs);count+=1
 return {'status':'PASS finite exact instances only','rational_projection_variance_and_profile_checks':count,'all_prefix_schedule_checks':branches,'closure_exponent_cases':exponents,'claims_not_certified':['universal analysis','A','external-paper proofs','substantiality','priority','human review','formal certification']}
if __name__=='__main__':
 import json
 print(json.dumps(check(),indent=2))
