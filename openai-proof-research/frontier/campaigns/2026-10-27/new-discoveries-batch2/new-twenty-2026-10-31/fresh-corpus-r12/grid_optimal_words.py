from itertools import combinations
from pathlib import Path
import json
w=4
bad=[]
for t in combinations(range(12),3):
 a,b,c=[divmod(i,3) for i in t]
 if (b[0]-a[0])*(c[1]-a[1])==(c[0]-a[0])*(b[1]-a[1]):continue
 d=[(u[0]-v[0])**2+(u[1]-v[1])**2 for u,v in combinations([a,b,c],2)]
 if len(set(d))<3:bad.append(sum(1<<i for i in t))
good=[s for s in range(4096) if all(s&t!=t for t in bad)]
trans={}
for s in good:trans.setdefault(s&511,[]).append((s>>3,(s>>9).bit_count(),s>>9))
# keep words at optimal size only with backward suffix bounds
rows=[]
for n in [7,9,11,13,15]:
 dp={s:(s.bit_count(),[(s&7,(s>>3)&7,s>>6)]) for s in range(512) if all(s&t!=t for t in bad)}
 for i in range(3,n):
  nd={}
  for s,(v,words) in dp.items():
   for t,c,a in trans.get(s,[]):
    nv=v+c
    if t not in nd or nd[t][0]<nv:nd[t]=(nv,[])
    if nd[t][0]==nv:nd[t][1].extend(ws+(a,) for ws in words)
  dp=nd
 m=max(v for v,ws in dp.values());words=[ws for v,wss in dp.values() if v==m for ws in wss]
 rows.append({'n':n,'local_maximum':m,'words':words});print(n,m,len(words));print(words[:8])
Path(__file__).with_name('grid-optimal-words.json').write_text(json.dumps(rows,indent=2))
