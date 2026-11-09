import numpy as np,itertools as it,json,time
from pathlib import Path
D=Path(__file__).resolve().parents[1];results=[]
for m,cap in [(5,3)]:
 masks=range(1<<m);subs=[[t for t in masks if t&s==t] for s in masks]
 # All antichains excluding empty family and empty set; encode upward Delta by bitmask.
 ants=[()]
 for s in range(1,1<<m):ants += [a+(s,) for a in ants if all((t&s)!=t and (t&s)!=s for t in a)]
 deltas=[tuple(s for s in masks if any(s&t==t for t in a)) for a in ants if a]
 import random
 deltas=random.Random(103).sample(deltas,1000)
 seen={};checked=compatible=0;bad=[]
 for rev in it.combinations_with_replacement(range(cap+1),m):
  g=rev[::-1]+(0,)
  if not g[0]:continue
  h=[sum(g[:i]) for i in range(m+1)];H=[h[s.bit_count()] for s in masks]
  vec=np.array(list(it.product(range(g[0]+1),repeat=m)),dtype=np.int16)
  sums=np.array([vec[:,[j for j in range(m) if s>>j&1]].sum(axis=1) for s in masks])
  B=[];up=[]
  for s in masks:
   valid=(sums[s]==H[s])&(sums[-1]==sums[s])
   for t in subs[s]:valid &= sums[t]<=H[t]
   b=vec[valid]; B.append(b)
   u=np.zeros(len(vec),dtype=bool)
   for v in b:u |= np.all(vec>=v,axis=1)
   up.append(u)
  sig=tuple(g[i-1]>g[i] for i in range(1,m+1))
  for delta in deltas:
   ds=set(delta)
   if any(H[y]>=H[x] for x in delta for y in subs[x] if y not in ds):continue
   if any(H[x&y]+H[x|y]>=H[x]+H[y] for x in delta for y in delta if x&y not in ds):continue
   compatible+=1
   auth=np.logical_or.reduce([up[x] for x in delta]);hier=[]
   for y in range(m):
    for x in range(m):
     if x==y:continue
     v=vec[auth&(vec[:,y]>0)&(vec[:,x]<g[0])].copy();v[:,y]-=1;v[:,x]+=1
     idx=sum(v[:,j]*(g[0]+1)**(m-1-j) for j in range(m))
     hier.append(bool(np.all(auth[idx])))
   key=(sig,delta); val=tuple(hier);checked+=1
   if key in seen and seen[key][0]!=val:bad.append(dict(g=g,other=seen[key],delta=delta,hierarchy=val))
   seen[key]=(val,g)
  print('progress',m,g,compatible,flush=True)
 results.append(dict(m=m,g0_max=cap,nonincreasing_sequences=mathcomb if False else len(list(it.combinations_with_replacement(range(cap+1),m)))-1,monotone_families=len(deltas),compatible_instances=compatible,signature_delta_classes=len(seen),violations=bad))
 (D/'outputs/polymatroid-deep.json').write_text(json.dumps(results,indent=2)+'\n')
 print('RESULT',results[-1],flush=True)
