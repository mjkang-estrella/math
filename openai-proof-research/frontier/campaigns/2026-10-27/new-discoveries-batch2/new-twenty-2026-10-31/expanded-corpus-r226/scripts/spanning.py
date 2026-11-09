from collections import deque
from itertools import combinations
import json,sys,time
from pathlib import Path
L=Path(__file__).resolve().parents[1]; lo=int(sys.argv[1]); hi=int(sys.argv[2]); out=[]
for k in range(lo,hi+1):
 n=2*k; best=10**9; witness=None; count=0
 # Every two-element subset, including zero and nongenerators; no quotient assumed.
 for a,b in combinations(range(2*n),2):
  ax,ay=divmod(a,n);bx,by=divmod(b,n);steps=((ax,ay),(ax,(-ay)%n),(bx,by),(bx,(-by)%n))
  dist=[-1]*(2*n);dist[0]=0;q=[0]
  for z in q:
   x,y=divmod(z,n)
   for dx,dy in steps:
    w=(x^dx)*n+(y+dy)%n
    if dist[w]<0:dist[w]=dist[z]+1;q.append(w)
  count+=1
  if len(q)==2*n and max(dist)<best:best=max(dist);witness=[a,b]
 predicted=next(s for s in range(1,2*k+2) if (s%2 and 2*k<=s*s-1) or (not s%2 and (2*k<=s*s-s or (2*k<=s*s and ((s%4==0 and k%2==0) or (s%4==2 and k%4==2))))))
 row=dict(k=k,subsets=count,min_radius=best,predicted=predicted,witness=witness);print(json.dumps(row),flush=True);out.append(row)
 if best!=predicted:print('MISMATCH',flush=True);break
(L/f'inputs/spanning-{lo}-{hi}.json').write_text(json.dumps(out,indent=2)+'\n')
