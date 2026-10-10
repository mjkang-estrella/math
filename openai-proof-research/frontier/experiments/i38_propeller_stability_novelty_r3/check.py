"""Exact finite bookkeeping for the analytic comparison in the R3 review.
Not a numerical proof of Theorem P, of compactness, or of novelty.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
def run():
 n=0
 # Integral_0^(z/a) (z-a*r)*r dr = z^3/(6*a^2).
 for z in [Q(0),Q(1,100),Q(1,3),Q(1),Q(10)]:
  for a in [Q(1,16),Q(1,4),Q(1),Q(3)]:
   t=z/a;assert z*t*t/2-a*t*t*t/3==z**3/(6*a*a);n+=1
 # The elementary splitting inequality used with a common head displacement.
 def pos(x):return max(Q(0),x)
 for a in [Q(i,3) for i in range(7)]:
  for b in [Q(i,4) for i in range(7)]:
   for t in [Q(i,5) for i in range(16)]:
    assert pos(a+b-t)<=pos(a-t/2)+pos(b-t/2);n+=1
 # Arbitrarily many genuinely active extra directions: exact Gram spectrum.
 rows=[]
 for N in [1,2,3,10,100,10000]:
  for E in [Q(1,100),Q(1,10000),Q(1,10**8)]:
   eig_head=(1-E)/2;eig_tail=E/N
   assert eig_head>0 and eig_tail>0
   assert 2*eig_head+N*eig_tail==1
   assert (1-E)/3+2*(-(1-E)/6)==0
   rows.append({'extra_labels':N,'E':str(E),'head_nonzero_eigenvalue':str(eig_head),'tail_eigenvalue':str(eig_tail),'normalized_partition_deficit_upper_bound':str(E)})
   n+=3
 # h^2=1/48: alternate activation coefficient 128 E|G|^3 < 400,
 # since (E|G|^3)^2=8/pi < 8/3 and 128^2*(8/3)<400^2.
 assert Q(128**2*8,3)<400**2;n+=1
 return {'status':'PASS','exact_finite_checks':n,'active_support_examples':rows,'analytic_not_computational_obligations':['positive Gaussian measure of each open winning cone','score/partition duality','Gaussian third absolute moment','Rayleigh density upper bound','uniform Gram compactification','significance comparison']}
if __name__=='__main__':
 out=run();Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='active_support_examples'},indent=2))
