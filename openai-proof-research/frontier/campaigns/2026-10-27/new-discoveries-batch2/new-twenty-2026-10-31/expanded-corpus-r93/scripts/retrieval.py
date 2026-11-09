import itertools,functools,json,sys
from fractions import Fraction as F
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def comps(t,n):
 if n==1:yield (t,);return
 for a in range(t+1):
  for b in comps(t-a,n-1):yield (a,)+b
k=3;vectors=range(8)
subs={1};todo=[1]
while todo:
 s=todo.pop()
 for v in vectors:
  new=s
  for u in vectors:
   if s>>u&1:new|=1<<(u^v)
  if new not in subs:subs.add(new);todo.append(new)
ordered=sorted(subs,key=int.bit_count,reverse=True)
trans={}
for s in subs:
 for v in vectors:
  t=s
  for u in vectors:
   if s>>u&1:t|=1<<(u^v)
  trans[s,v]=t
out=[]
for n in range(3,11):
 count=0;maximum=F(0);arg=None
 for cs in comps(n,8):
  span=1
  for v,c in enumerate(cs):
   if c:span=trans[span,v]
  if span!=255:continue
  Es=[]
  for target in [3,85]: # bitsets {0,1} and {0,2,4,6}
   e={}
   for s in ordered:
    if s&target==target:e[s]=F(0);continue
    stuck=sum(c for v,c in enumerate(cs) if trans[s,v]==s)
    if stuck==n:e[s]=None;continue
    e[s]=(n+sum(c*e[trans[s,v]] for v,c in enumerate(cs) if c and trans[s,v]!=s))/(n-stuck)
   Es.append(e[1])
  ratio=1/Es[0]+2/Es[1];count+=1
  if ratio>maximum:maximum=ratio;arg=cs
  if ratio>1:print('WITNESS',n,cs,Es,ratio,flush=True)
 print('COMPLETE',n,count,str(maximum),arg,flush=True);out.append([n,count,str(maximum),arg]);(D/'outputs/retrieval.json').write_text(json.dumps(out))
