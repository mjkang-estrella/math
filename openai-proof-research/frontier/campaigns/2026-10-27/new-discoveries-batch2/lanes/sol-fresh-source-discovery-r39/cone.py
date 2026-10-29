# All helper definitions execute their own hard memory/CPU/alarm caps.
from check import *
import random
rng=random.Random(39); accepted=0; witness=None
for trial in range(1600):
 n=rng.randrange(5,13);q=[1]
 for j in range((n-2)//2):
  # Each real quadratic has positive coefficients, hence strict left stability.
  q=mul(q,[F(rng.choice([1,2,5,10,25,100]),rng.choice([1,5,25])),F(rng.choice([1,2,5,10,25,100]),rng.choice([1,5,25])),1])
 while len(q)<n-1:q=mul(q,[F(rng.choice([1,5,25]),rng.choice([1,5,25])),1])
 if any(q[j]**2<q[j-1]*q[j+1] for j in range(1,len(q)-1)):continue
 accepted+=1;image=stepq(q,n)
 if any(v<=0 for v in routh(image)):
  witness={'n':n,'q':[str(v) for v in q],'image':[str(v) for v in image],'routh':[str(v) for v in routh(image)]};break
out={'trials':trial+1,'logconcave_hurwitz_inputs':accepted,'obstruction':witness,'scope':'bounded diagnostic; no universal inference'}
(b/'cone.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
