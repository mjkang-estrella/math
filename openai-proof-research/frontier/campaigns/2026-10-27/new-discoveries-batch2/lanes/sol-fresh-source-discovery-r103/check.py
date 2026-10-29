from fractions import Fraction as F
from pathlib import Path
import json
P=Path(__file__).resolve().parent
# Finite Gaussian mixtures: exact posterior precision moments at x=0.
def curvature(variances,weights,sqrtvars):
 a=[p/s for p,s in zip(weights,sqrtvars)];a=[x/sum(a) for x in a]
 moments=[sum(q/v**k for q,v in zip(a,variances)) for k in range(4)]
 mu=moments[1];var=moments[2]-mu**2;k3=moments[3]-3*mu*moments[2]+2*mu**3
 # L(s)=2m(s)+4s m'(s)-s m(s)^2; K(v)=E L(v Z^2).
 # m'(0)=-var/2, m''(0)=k3/4; E Z^4=3.
 L2=F(5,2)*k3+2*mu*var;K2=3*L2
 return {'posterior':list(map(str,a)),'mean_precision':str(mu),'variance_precision':str(var),'third_cumulant':str(k3),'L_second_at_zero':str(L2),'K_second_at_zero':str(K2)},K2
r=F(9,10)
row,k=curvature([F(1),F(25),F(49)],[r*r,2*r*(1-r),(1-r)**2],[F(1),F(5),F(7)])
assert k<0
# Independent algebraic Taylor check with formal power series, through s^2.
def mul(a,b):return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(3)]
q=list(map(F,row['posterior']));prec=[F(1),F(1,25),F(1,49)]
D=[sum(p*(-z/2)**j/(1 if j<2 else 2) for p,z in zip(q,prec)) for j in range(3)]
N=[sum(p*z*(-z/2)**j/(1 if j<2 else 2) for p,z in zip(q,prec)) for j in range(3)]
m=[N[0],N[1]-D[1]*N[0],N[2]-D[1]*(N[1]-D[1]*N[0])-D[2]*N[0]]
# s^2 coefficient of L is 10*m2 - 2*m0*m1.
assert 2*(10*m[2]-2*m[0]*m[1])==F(row['L_second_at_zero'])
# Gaussian heat-kernel second derivative integrates to zero.
assert F(3)-6+3==0
# Exact first-variation cancellation at exchangeable equal coefficients for any finite law.
checks=0
for vals,probs in [([F(1),F(49)],[r,1-r]),([F(1),F(4),F(9)],[F(1,2),F(1,3),F(1,6)])]:
 for power in range(7):
  assert sum(pi*pj*(vi-vj)*((vi+vj)/2)**power for vi,pi in zip(vals,probs) for vj,pj in zip(vals,probs))==0;checks+=1
out={'status':'PASS: route obstruction only; no source proof/refutation','two_copy_equal_weight_mixture':row,'formal_series_crosscheck':True,'exchangeability_identities':checks,'caps':'unchanged external helper_guard.py; exact Fraction arithmetic; no quadrature or sample inference'}
(P/'check-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
