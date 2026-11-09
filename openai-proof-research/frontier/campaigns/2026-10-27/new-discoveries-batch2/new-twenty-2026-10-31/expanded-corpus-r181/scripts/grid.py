from itertools import product,permutations
from pathlib import Path
import json,collections
D=Path(__file__).resolve().parents[1]
verts=list(product(range(2),range(2),range(3)));n=len(verts);edges=[(a,b) for a in range(n) for b in range(a+1,n) if sum(abs(x-y) for x,y in zip(verts[a],verts[b]))==1];m=len(edges)
darts=[(a,b) for e in edges for a,b in [e,e[::-1]]];di={d:i for i,d in enumerate(darts)}
rots=[]
for v in range(n):
 ds=[di[v,w] for w in range(n) if (v,w) in di]
 rots.append([list(zip(seq,seq[1:]+seq[:1])) for p in permutations(ds[1:]) for seq in [[ds[0]]+list(p)]])
hist=collections.Counter();example=None
for choices in product(*rots):
 succ=[0]*(2*m)
 for pairs in choices:
  for a,b in pairs:succ[a^1]=b
 seen=0;faces=0
 for i in range(2*m):
  if seen>>i&1:continue
  faces+=1;j=i
  while not seen>>j&1:seen|=1<<j;j=succ[j]
 g=(2-n+m-faces)//2;hist[g]+=1
 if g==0 and example is None:example=choices
out={'parameters':[1,1,2],'vertices':n,'edges':m,'rotation_systems':sum(hist.values()),'genus_histogram':dict(hist),'minimum':min(hist),'known_source_case':True,'planar_rotation':example}
(D/'outputs/grid.json').write_text(json.dumps(out,indent=2));print(out['rotation_systems'],hist)
