from pathlib import Path
from collections import defaultdict
import json
L=Path(__file__).resolve().parent
# All prefix normal binary words beginning with 1, total lengths through 20.
levels={1:[(1,(0,1))]}; sig=defaultdict(lambda:[0]*17); counts={}
for n in range(1,25):
 ws=levels.pop(n);counts[n]=len(ws)
 for w,p in ws:
  for k in range(max(1,n-16),min(8,n-1)+1):sig[(k,w>>(n-k))][n-k]+=1
 print('level',n,len(ws),flush=True)
 if n==24:break
 nxt=[]
 for w,p in ws:
  nxt.append((w*2,p+(p[-1],)))
  q=p+(p[-1]+1,)
  if all(q[-1]-q[n+1-k]<=q[k] for k in range(1,n+2)):nxt.append((w*2+1,q))
 levels[n+1]=nxt
coll=defaultdict(list)
for (k,w),s in sig.items():
 if k<=8 and s[1]:coll[tuple(s[1:])].append(format(w,'0'+str(k)+'b'))
a=[{'words':v,'counts':k} for k,v in coll.items() if len(v)>1]
(L/'word24-results.json').write_text(json.dumps({'total_length_max':24,'prefix_length_max':8,'extension_length_max':16,'level_counts':counts,'collisions':a},indent=2));print('collision groups',len(a));print(a[:20])
