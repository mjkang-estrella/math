from pathlib import Path
from itertools import product
import random,json
D=Path(__file__).resolve().parents[1];rng=random.Random(241)
def hit(x,t,rev=False):
 if rev:x=tuple(8-v for v in x[::-1])
 n=len(x)+2;v=[0]*n;v[0]=1
 for k in range(t):
  w=[0]*n;w[1]+=8*v[0]
  for i,a in enumerate(x,1):w[i+1]+=a*v[i];w[i-1]+=(8-a)*v[i]
  w[-1]+=8*v[-1];v=w
 return v[-1]
for n in range(3,15):
 xs=product(range(1,8),repeat=n-2) if n<=6 else (tuple(rng.randrange(1,8) for _ in range(n-2)) for j in range(1000))
 cases=0;equal=0;better=0
 base={t:hit((4,)*(n-2),t) for t in range(n-1,2*n-2)}
 for x in xs:
  for t in base:
   value=min(hit(x,t),hit(x,t,True));cases+=1
   if value>base[t]:better+=1;print('BETTER',n,t,x,value,base[t],flush=True)
   if value==base[t] and x!=(4,)*(n-2):equal+=1;print('TIE',n,t,x,value,flush=True)
 print('ROW',n,'cases',cases,'better',better,'nonuniform_equal',equal,flush=True)
