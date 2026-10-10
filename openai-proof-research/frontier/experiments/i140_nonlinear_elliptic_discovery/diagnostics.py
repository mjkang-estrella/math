"""New finite exact arithmetic checks only; not universal mathematics."""
from fractions import Fraction as F
from collections import Counter

def run():
 c=Counter()
 def ck(name,test):
  if not test:raise AssertionError(name)
  c[name]+=1
 for n in range(3,13):
  for p in [F(1,2),F(3,4),F(3,2),F(2),F(3),F(4)]:
   for q in [F(1,2),F(3,4),F(3,2),F(2),F(3),F(4)]:
    if p*q<=1:continue
    for A,B in [(F(0),F(0)),(F(-3,2),F(1,3)),(F(2),F(3))]:
     al=(2+A+p*(2+B))/(p*q-1);be=(2+B+q*(2+A))/(p*q-1)
     ell=1/(q+1);m=1/(p+1);ga=ell*(n+B)+m*(n+A)-(n-2)
     ck('coupled_weighted_scaling',p*be==al+2+A and q*al==be+2+B and al>0 and be>0)
     ck('energy_exponent_gap',ga==(1-ell-m)*(al+be+2-n) and n+B-(q+1)*al==n-2-al-be)
     for da,db in [(F(0),F(0)),(F(1,7),F(2,9))]:
      c1=ell*(n+B-db)-(n-2);c2=m*(n+A-da);G=ga-ell*db-m*da
      ck('virial_variation_budget',c1+c2==G)
    C,D=F(3,7),F(-2,5)
    S=(C+p*D)/(p*q-1);T=(D+q*C)/(p*q-1)
    ck('positive_coefficient_log_normalization',S+C-p*T==0 and T+D-q*S==0)
 for n in range(3,13):
  for j in range(1,6):
   k=F(n-2,4)+F(j,6)*F(n-2,4);p=1+1/k
   ck('subcritical_profile_range',F(n,n-2)<p<F(n+2,n-2))
   for t in [F(0),F(1,7),F(1),F(3),F(100)]:
    left=2*k*n*(1+t)-4*k*(k+1)*t
    right=2*k*(n+(n-2*k-2)*t)
    a=right/(1+t)
    ck('radial_exact_coefficient',left==right and 2*k*(n-2*k-2)<=a<=2*k*n)
  k=F(n-2,2);p=F(n+2,n-2)
  ck('talenti_profile_factor',k*(p-1)==2 and 2*k*n==n*(n-2) and n-2*k-2==0)
 for t in [F(0),F(1,9),F(1),F(9),F(100)]:
  a=F(2,9)*(9+t)/(1+t)
  ck('O140b_coefficient_bounds',F(2,9)<=a<=2)
 ck('O140b_modulus_jump',2-F(2,9)*10/2==F(8,9))
 ck('O140b_pohozaev_factor',-(F(3,5)-F(1,2))*5==-F(1,2))
 for d in range(2,9):
  for p in range(d+1,d+12):
   beta=F(p-d,p-1)
   lap=beta*(beta+d-2);infty=beta**3*(beta-1)
   ck('p_lift_equation_obstruction',beta**2*lap+(p-2)*infty==0 and lap>0)
 for N in range(2,25):
  edges={(i,j) for i in range(N) for j in range(N) if i!=j and (i+j)%5==0}
  vertices={v for e in edges for v in e}
  ck('directed_endpoint_deletion',len(vertices)<=len(edges))
  pairs=[(i,j) for i in range(N) for j in range(N) if i!=j]
  ck('moved_site_ordered_factor',sum(i==0 or j==0 for i,j in pairs)==2*(N-1))
 return {'status':'PASS','arithmetic':'integers and fractions.Fraction','checks':dict(sorted(c.items())),'scope':'new finite algebra checks only; not PDE existence/regularity, arbitrary meshes, external results, novelty or acceptance'}
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2,sort_keys=True))
