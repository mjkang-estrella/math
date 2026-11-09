from pathlib import Path
import json
L=Path(__file__).resolve().parent
def T(n):return [(x-1,y-1,x+y//2-1) for y in range(1,n+1) for x in range(1,n-y//2+1)]
out=[]
for n in (12,13):
 ts=T(n);size=1<<(n-1);full=(1<<n)-1
 def norm(a):return (a if not a&1 else a^full)>>1
 masks=sorted(set(norm(((1<<(b-a+1))-1)<<(a-1)) for a in range(1,n+1) for b in range(a,n+1))-{0})
 vals=[sum(((m*2>>x)&1)==((m*2>>y)&1)==((m*2>>z)&1) for x,y,z in ts) for m in range(size)]
 parent=list(range(size))
 def find(x):
  while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
  return x
 for m in range(size):
  for f in masks:
   j=m^f
   if vals[m]==vals[j]:parent[find(m)]=find(j)
 comps={}
 for m in range(size):
  r=find(m);d=comps.setdefault(r,dict(M=vals[m],size=0,has_exit=False,representative=m));d['size']+=1
  if any(vals[m^f]<vals[m] for f in masks):d['has_exit']=True
 sinks=[d for d in comps.values() if not d['has_exit'] and d['M']>min(vals)]
 for d in sinks:
  d['word']=''.join(str((d['representative']*2>>i)&1) for i in range(n))
 out.append(dict(n=n,states=size,distinct_interval_masks=len(masks),components=len(comps),suboptimal_sink_components=sinks))
(L/'plateau.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
