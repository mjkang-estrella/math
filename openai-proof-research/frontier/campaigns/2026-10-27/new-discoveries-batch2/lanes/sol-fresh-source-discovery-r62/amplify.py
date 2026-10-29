from check import es,admiss,delta
from fractions import Fraction as Q
import json,pathlib
out=[]
for N in range(1,81):
 a=[2,3]*N;b=[1,4]*N
 d=2*Q(35,99)**N-Q(1,3)**N-Q(9,25)**N
 ok=admiss(a,b)
 out.append(dict(N=N,admissible=ok,delta1=str(d),negative=d<0))
 if ok and d<0:
  assert delta(a,b,Q(1),Q(1,2),Q(1,2),1)==d
  break
pathlib.Path('amplification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out[-1]))
