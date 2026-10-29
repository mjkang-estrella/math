from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json, hashlib, shutil
L=Path(__file__).resolve().parent; P=L.parent
# Independent signed ROW propagation, rather than the candidate column recurrence.
a=[9,8,7,6,5,4,3,4,5,6,7,8];w=[F(6-x,72) for x in a];v=w[:]; t=F(48,5);u=F(0)
for k in range(161):
 u+=sum(v)*t**k/factorial(k)
 v=[-(1+F(a[j],60))*v[j]+v[(j-1)%12] for j in range(12)]
z=t*F(43,20);E=F(1,4)*z**161/factorial(161)/(1-z/162)
assert u+E < -F(1,25000)
# Independent larger, deliberately looser coupling envelope.
# h<7/10^12,t<5; sqrt(ht)<6/10^6; integral sqrt(hs)ds<(10/3)*6/10^6.
h=F(7,10**12);Fbound=5*h+F(10,3)*F(6,10**6)
err=h/2+F(5,4)*Fbound
assert 5*h < F(6,10**6)**2
assert err < F(1,3888)
assert F(1,1944)-err > F(1,3888)
# Taylor-certified elementary e<3 without evaluating e: first 4 terms + geometric tail.
eupper=sum((F(1,factorial(k)) for k in range(4)),F(0))+F(1,24)/(1-F(1,5))
assert eupper <3
# J(a)=sum a^(2k+1) E cos^(2k+2)/(2k+1)!, coefficient positivity and leading term.
coeff=[F(factorial(2*k+2),4**(k+1)*factorial(k+1)**2*factorial(2*k+1)) for k in range(12)]
assert coeff[0]==F(1,2) and all(c>0 for c in coeff)
# Symbolic sign check uses sqrt(2)^2=2: (epsilon/mu)*cos(t/2)*a/2=-1/8.
assert F(1,2)*(-F(1,2))*F(1,2)*2/2 == -F(1,8)
res={'r90_row_taylor_upper':str(u+E),'r90_upper_below_minus_1_25000':True,'coupling_F_upper':str(Fbound),'coupling_gap_error_upper':str(err),'coupling_error_below_1_3888':True,'e_upper':str(eupper),'J_first_12_positive_coefficients':[str(c) for c in coeff],'analytic_proof_required':'Symmetry, all-series positivity/integration or x*sinh(ax)>=a*x^2, and Poisson variance/Cauchy-Schwarz are proved in review.md; finite coefficients alone are not those proofs.'}
(L/'independent-exact-bridge-checks.json').write_text(json.dumps(res,indent=2))
paths=['root-gamma-level-r1/PROOF.md','root-gamma-level-formal-r1/PERSPECTIVE-OBJECTION.md','root-gamma-level-formal-r1/INVESTMENT-DECISION-R2.md','root-arcsinh-positive-r1/PROOF.md','root-arcsinh-review-adjudication-r1/ADJUDICATION.md','sol-fresh-source-discovery-r82/PROOF.md','sol-fresh-source-discovery-r89/PROOF.md','root-dewitt-rank-exclusion-r1/EXCLUSION.json','root-bajnok-beatty-exclusion-r1/EXCLUSION.json','sol-edge-irregulator-manuscript-packet-r1/packet/paper.tex']
records={}
for p in paths:
 s=P/p
 if not s.exists():continue
 b=s.read_bytes();records[p]=hashlib.sha256(b).hexdigest();q=L/'context'/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
for p in ['AGENTS.md','NEXT.md','ledger.json','prior-campaign-context.json']:
 b=(L/'context'/p).read_bytes(); records[p]=hashlib.sha256(b).hexdigest()
ledger=json.loads((L/'context/ledger.json').read_text());records['counting_standard']=ledger['counting_standard']
(L/'context-provenance.json').write_text(json.dumps(records,indent=2));print('Independent exact checks PASS')
