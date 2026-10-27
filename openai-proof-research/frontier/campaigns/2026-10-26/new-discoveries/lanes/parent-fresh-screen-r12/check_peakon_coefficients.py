"""Independent exact matrix checks of the prospective all-order trace expansion."""
import sympy as s
import json,random
from pathlib import Path
rng=random.Random(372008);checks=0
for N in range(1,7):
 for trial in range(4):
  u=s.Matrix([s.Rational(rng.randrange(1,9),rng.randrange(1,6)) for _ in range(N)])
  v=s.Matrix([s.Rational(rng.randrange(1,9),rng.randrange(1,6)) for _ in range(N)])
  B=s.Matrix(N,N,lambda i,j:u[i]*v[j]-v[i]*u[j] if i<j else 0)
  assert B-B.T==u*v.T-v*u.T
  T=(u*v.T+v*u.T)/2;A=(u*v.T-v*u.T)/2;S=B-A
  gamma=s.Rational(trial-1);z=s.Rational(trial+2)
  lam=(z*z-1)/(2*z+gamma);xi=(z*z+gamma*z+1)/(2*z+gamma)
  assert xi*xi==lam*lam+gamma*lam+1
  L=S+lam*T+xi*A
  maxm=11;H=[s.Rational(0)]*(maxm+1);P=s.eye(N)
  for k in range(1,maxm+1):H[k]=s.trace((T+gamma*A/2)*P);P=P*B
  powers=[s.Rational(0)]*(maxm+1);powers[0]=1
  expected=[s.Rational(0)]*(maxm+1)
  for j in range(1,maxm+1):
   powers=[sum(powers[a]*H[m-a] for a in range(m+1)) for m in range(maxm+1)]
   for m in range(1,maxm+1):expected[m]+=s.Rational(m,j)*lam**j*powers[m]
  P=s.eye(N)
  for m in range(1,maxm+1):
   P=P*L;assert s.trace(P)==expected[m],(N,trial,m);checks+=1
  t=s.symbols('t');actual=(s.eye(N)-t*L).det();predicted=1-lam*sum(H[k]*t**k for k in range(1,N+1));assert s.expand(actual-predicted)==0
out={'status':'PASS','exact_trace_cases':checks,'exact_characteristic_determinants':24,'dimensions':'1..6','orders':'1..11','generic_matrix_bridge':'arbitrary rational u,v and source spectral curve, not just sampled peakon positions','universal_proof':'PEAKON-PROPOSAL.md','formal_and_novelty_claim':False,'credit':0}
Path(__file__).with_name('peakon-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
