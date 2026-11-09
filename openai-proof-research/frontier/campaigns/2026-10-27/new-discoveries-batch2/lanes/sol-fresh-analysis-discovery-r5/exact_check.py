from fractions import Fraction as F
from math import comb
from pathlib import Path
import json,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
# Differentiate the q recurrence at a=0,c=1; q_n=1 there.
qa=[F(0)]; qc=[F(0)]
for n in range(1,41):
 qa.append(sum((F(k,k+1)+qa[n-k] for k in range(1,n+1)),F(0))/n)
 qc.append(sum((1+qc[n-k] for k in range(1,n+1)),F(0))/n)
 H=lambda n:sum((F(1,k) for k in range(1,n+1)),F(0))
 assert 1+qa[n]==H(n+1)
 assert qc[n]==H(n)
# Phi^(n)(0)=(-1)^n e^a q_(n+1); first variations are harmonic numbers.
for n in range(39):
 U=(-1)**n*(1+qa[n+1]);V=(-1)**(n+1)*qc[n+1]
 Unext=(-1)**(n+1)*(1+qa[n+2]);Vnext=(-1)**(n+2)*qc[n+2]
 assert U+Unext==F((-1)**(n+1),n+3)
 assert V+Vnext==F((-1)**n,n+2)
result={'status':'PASS','arithmetic':'Python fractions.Fraction only','q_parameter_derivatives_checked_through_n':40,'filtered_integral_coefficients_checked_through_n':38,'randomness':'none','RSS_limit_MiB':512,'full_source_result':False}
(Path(__file__).resolve().parent/'exact-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
