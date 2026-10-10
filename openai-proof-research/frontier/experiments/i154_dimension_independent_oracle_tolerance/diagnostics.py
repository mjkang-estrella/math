"""New finite rational tests only; never a universal mathematical certificate."""
from fractions import Fraction as F
import math
def run():
 cases=[]
 for den in [2,4,16,64]:
  h=F(1,den);q=1/(1+h);m=den
  a=F(7,3);energy=F(0)
  for j in range(m):
   theta=F(1,m-j);assert a==q**j*F(m-j,m)*F(7,3)
   energy+=q*q/(2*h)*theta*theta*a*a
   a=q*(1-theta)*a
  assert a==0 and energy<=F(7,3)**2/(2*h*m)
  # An admissible prescribed-mode quadratic V=3|x|^2/4 gives a Gaussian P_h.
  aq=1/(1+F(3,2)*h);v=h+1/(F(3,2)+1/h)
  variance=v*sum(aq**(2*j) for j in range(m))
  exact_kl=aq**(2*m)*F(7,3)**2/(2*variance)
  assert exact_kl<=F(7,3)**2/(2*h*m)
  eta=F(1,100);disp=3*h*eta
  one_kl=disp*disp/(2*(h/4));assert one_kl==18*h*eta*eta
  assert m*one_kl==18*eta*eta
  cases.append({'h':str(h),'m':m,'shift_energy':str(energy),'quadratic_exact_KL':str(exact_kl),'window_oracle_KL':str(m*one_kl)})
 # Exact finite-state disintegration: same next-state kernel preserves marginal KL/TV.
 p=[F(1,3),F(2,3)];q=[F(1,2),F(1,2)];L=[[F(1,4),F(3,4)],[F(2,5),F(3,5)]]
 pj=[p[i]*L[i][j] for i in range(2) for j in range(2)]
 qj=[q[i]*L[i][j] for i in range(2) for j in range(2)]
 assert sum(abs(a-b) for a,b in zip(pj,qj))==sum(abs(a-b) for a,b in zip(p,q))
 for i in range(2):
  for j in range(2):assert pj[2*i+j]/qj[2*i+j]==p[i]/q[i]
 # Internal transformed slot covariance is nonzero: delayed sampling alone is insufficient.
 Ds=F(8);v0=F(1,2);v1=F(-3,4);cov=-v0*v1/(4*Ds*Ds);assert cov!=0
 # Height constants are fixed before smallness; finite tests of both coefficients in (3).
 C=F(2);Lk=Pk=F(1);heights=[]
 for k in range(1,5):
  Lnext=8*C*C*Lk*(1+Lk);Pnext=8*C*C*Pk*(1+Lk)
  assert 2*C*Pk+2*C*C*Lk*Pk<=Pnext
  assert 2*C*Lk+2*C*C*Lk*Lk<=Lnext
  heights.append({'height':k,'L':str(Lnext),'P':str(Pnext)})
  Lk,Pk=Lnext,Pnext
 return {'status':'PASS','fixed_time_cases':cases,'joint_state_RN_and_TV':'exact rational identities','internal_transformed_covariance':str(cov),'height_constants':heights,'scope':'Finite instances only. No universal proof, contribution, acceptance, priority or human/formal certification.'}
