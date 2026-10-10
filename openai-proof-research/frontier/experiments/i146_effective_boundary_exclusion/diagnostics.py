"""New finite rational checks only; no PDE, universality or contribution certification."""
from fractions import Fraction as F
from collections import Counter

def run():
 c=Counter()
 for n in range(3,9):
  for p in [F(3,2),F(2),F(3),F(4)]:
   for q in [F(4,3),F(3,2),F(2),F(3)]:
    a=2*(p+1)/(p*q-1);b=2*(q+1)/(p*q-1)
    assert -(n+(2-n)*q+q*(n+(2-n)*p))/(p*q-1)==n-2-b
    assert n*(1-1/q)+(n-2-b)/q==n-a
    assert p*b==a+2 and q*a==b+2
    c['finite_ball_mass_and_L1_exponents']+=1
    for A,B in [(F(0),F(0)),(F(1,2),F(2)),(F(3),F(1))]:
     aa=(2+A+p*(2+B))/(p*q-1);bb=(2+B+q*(2+A))/(p*q-1)
     sigma=aa+bb+2-n;gamma=(n+A)/(p+1)+(n+B)/(q+1)-(n-2)
     assert gamma==(1-1/(p+1)-1/(q+1))*sigma
     assert A-(p+1)*bb==B-(q+1)*aa==-n-sigma
     for theta in [F(1),F(1,2),F(1,3)]:
      assert n-1+A+theta+1-p*bb-bb-1==theta-sigma-1
      assert n-2+2-aa-1-bb-1==-sigma
      c['weighted_sphere_curvature_holder_exponents']+=1
 for n in range(3,12):
  for j in range(1,11):
   theta=F(1,j);delta=theta/8;m=max(F(n+3),1/theta+1);k=n*(m+1);N=k+n+2
   assert (1-delta)**j>=F(1,2)
   assert N-1-k==n+1 and N-n-1+m>=N
   assert N-1-m*(n-2)==2*m+2*n+1
   assert N-m*(n-1)==m+2*n+2
   c['holder_retention_and_localization_powers']+=1
  for j in range(41):
   t=F(j,40)
   lap=-F(3,2)*(n+2)*(1-t)**2+6*t*(1-t)
   assert abs(lap)<=F(3,2)*(n+6)
   c['first_moment_cutoff_laplacian_samples']+=1
 for n in [4,6,8]:
  for a in [F(1,8),F(1),F(2)]:
   for b in [F(1,5),F(1),F(3)]:
    for h in [F(1,3),F(1),F(4)]:
     r2=h*h+(a-b)**2;s2=h*h+(a+b)**2
     G=r2**(1-n//2)-s2**(1-n//2)
     dilation=(n-2)*(r2*r2**(-n//2)-s2*s2**(-n//2))
     assert G>0 and dilation==(n-2)*G
     JG=(n-2)*h*h*(r2**(-n//2)-s2**(-n//2))
     assert 0<=JG<=n*h*h/r2*G
     c['reflected_dilation_and_tangential_ratio']+=1
     for tang,normal in [(F(1),F(1)),(F(-1),F(1)),(F(1,3),F(-1,2))]:
      d=-(n-2)*((tang*h*h+normal*(a-b)**2)*r2**(-n//2)-(tang*h*h+normal*(a+b)**2)*s2**(-n//2))
      assert abs(d)<=(n+2)*G
      c['tangent_linear_vector_bound_samples']+=1
 for ca,cb in [(F(5,3),F(7,4)),(F(2),F(3))]:
  for n in range(3,8):
   for I,df,dg in [(F(7),F(2),F(-3)),(F(1),F(-1,2),F(1,3))]:
    u=I+df;v=I+dg;gamma=ca+cb-(n-2)
    lhs=ca*u+cb*v-(n-2)*I
    rhs=gamma*(u+v)/2+(ca-cb)*(u-v)/2+(n-2)*(df+dg)/2
    assert lhs==rhs;c['cross_energy_elimination']+=1
 assert F(5,5)+F(25,12)-3==F(1,12) and 4>F(7,3)
 c['strict_target_point_outside_kelvin_rectangle']=1
 return {'status':'PASS','arithmetic':'integers and fractions.Fraction','checks':dict(sorted(c.items())),'scope':'finite identities and samples only; not PDE inequalities, regularity, all-function coverage, numerical exclusion, external proofs, novelty or acceptance'}
