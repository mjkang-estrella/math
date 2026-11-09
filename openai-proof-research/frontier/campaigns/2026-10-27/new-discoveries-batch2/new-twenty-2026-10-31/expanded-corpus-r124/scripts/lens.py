import sys,pathlib,itertools,math,json
sys.dont_write_bytecode=True
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'fresh-corpus-r10/pydeps'))
import numpy as np
from functools import lru_cache
@lru_cache(None)
def sig(q,s):
 a=np.zeros((q,len(s)*q+1),dtype=np.int64);a[0,0]=1;used=0
 for t in s:
  b=np.zeros_like(a)
  for r in range(q):
   v=np.roll(a,r*t,axis=0)
   for deg in [r,q-r]:
    b[:,deg:deg+used+1]+=v[:,:used+1]
  a=b;used+=q
 return tuple(int(x) for x in a[0])
out=[]
for q in range(2,31):
 groups={};tested=0;collisions=0;bad=[]
 for s in itertools.combinations_with_replacement(range(q//2+1),3):
  if math.gcd(q,*s)>1:continue
  tested+=1;v=sig(q,s)
  if v in groups:
   collisions+=1;t=groups[v]
   for e in range(2,q):
    if q%e==0 and sig(e,tuple(x%e for x in s))!=sig(e,tuple(x%e for x in t)):bad.append([s,t,e])
  else:groups[v]=s
 o=dict(q=q,dimension=5,effective_sign_normalized_parameter_tuples=tested,collisions=collisions,failures=bad);out.append(o);print(o,flush=True)
(D/'outputs/lens.json').write_text(json.dumps(out,indent=2))
