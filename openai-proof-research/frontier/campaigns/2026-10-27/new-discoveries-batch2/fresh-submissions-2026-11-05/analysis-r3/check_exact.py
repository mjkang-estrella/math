from fractions import Fraction as F
from math import factorial,comb
from pathlib import Path
import json
# Exact scalar sign-defect, deliberately excluded from discovery.
A,B,C,q,s=-2,-1,-1,3,F(1)
lhs=C*(A**q-B**q)
rhs=F(q,2)*(s*max(A-B,0)**2*abs(A)**(q-1)+s*min(A-B,0)**2*abs(B)**(q-1)+max(C,0)**2/s*abs(A)**(q-1)+min(C,0)**2/s*abs(B)**(q-1))
assert lhs==7 and rhs==3
# Mellin finite sums when a=gamma*p*delta is integral.
rows=[]
for delta in range(2,10):
 for gamma in [F(1,4),F(1),F(4)]:
  for a in range(1,13):
   def J(k):return sum(F(comb(a,j)*factorial(k+j-1),1)/gamma**j/delta**(k+j) for j in range(a+1))
   ratio=J(delta-1)*J(delta+1)/J(delta)**2
   bound=F(delta,delta-1)
   assert ratio<=bound
   rows.append((delta,str(gamma),a,str(bound-ratio)))
# Artificial old Schur row s_(2) in m=4 transition has a pole at d'=0.
def residue(a,b):return 48*a*a*4*b*(a+3*b)*(2*a+2*b)*(3*a+b)
pole=F(residue(1,2)-residue(2,1),2-1)
assert pole==-80640
out={'scalar_trace_excluded':{'lhs':lhs,'rhs':str(rhs),'q':q,'s':str(s)},'mellin_exact_cases':len(rows),'mellin_all_pass':True,'mellin_min_slack':str(min(F(v[3]) for v in rows)),'plucker_artificial_transition_pole_at_a1_b2':str(pole),'all_checks_pass':True}
Path(__file__).with_name('exact-diagnostics.json').write_text(json.dumps(out,indent=2));print(out)
