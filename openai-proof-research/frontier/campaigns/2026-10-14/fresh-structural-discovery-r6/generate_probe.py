# Copyright (c) 2026 Myeongjin Kang. MIT License.
from explore import *
from itertools import combinations
from random import Random

def embed_prism(m):
 n,e=prism(m)
 return n,e,[list(range(m)),list(range(m,2*m))]+[[i,(i+1)%m,m+(i+1)%m,m+i] for i in range(m)]
def expand(g,fi,i,j):
 n,e,faces=g;f=faces[fi];l=len(f)
 u,v=f[i],f[(i+1)%l];y,x=f[j],f[(j+1)%l]
 rem={tuple(sorted((u,v))),tuple(sorted((x,y)))}
 a,b,c,d=range(n,n+4)
 es=edgeset([z for z in e if z not in rem]+[(u,a),(v,b),(x,c),(y,d),(a,b),(b,d),(d,c),(c,a)])
 fs=[]
 def segment(start,end):
  out=[f[start%l]]
  while start%l!=end%l:start+=1;out.append(f[start%l])
  return out
 for k,h in enumerate(faces):
  if k==fi:continue
  z=[]
  for t,p in enumerate(h):
   q=h[(t+1)%len(h)];z.append(p)
   if {p,q}=={u,v}:z += [a,b] if p==u else [b,a]
   if {p,q}=={x,y}:z += [c,d] if p==x else [d,c]
  fs.append(z)
 fs.extend([[a,b,d,c],segment(i+1,j)+[d,b],segment(j+1,i)+[a,c]])
 assert len(fs)==n//2+4
 # Every edge is on exactly two supplied faces, proving the combinatorial sphere embedding.
 occ={z:0 for z in es}
 for h in fs:
  assert len(set(h))==len(h) and len(h)%2==0
  for p,q in zip(h,h[1:]+h[:1]):occ[tuple(sorted((p,q)))]+=1
 assert set(occ.values())=={2}
 return n+4,es,fs

def conn3(n,e):
 adj=[set() for _ in range(n)]
 for u,v in e:adj[u].add(v);adj[v].add(u)
 for deleted in [()]+[(u,) for u in range(n)]+list(combinations(range(n),2)):
  rem=set(range(n))-set(deleted);seen={min(rem)};q=list(seen)
  while q:
   for v in adj[q.pop()]&rem-seen:seen.add(v);q.append(v)
  if seen!=rem:return False
 return True
if __name__=='__main__':
 rng=Random(6126);g=embed_prism(4);total=0
 for k in range(160):
  if k%4==0:g=embed_prism(rng.choice([4,6,8]))
  opts=[(f,i,j) for f,h in enumerate(g[2]) for i,j in combinations(range(len(h)),2) if (j-i)%2==0]
  h=expand(g,*rng.choice(opts));n,e,faces=h
  if not conn3(n,e):continue
  g=h;c=hcs(n,e);r=rank([[x-y for x,y in zip(a,c[0])] for a in c[1:]]) if c else -1
  total+=1
  print(k,n,len(c),r,n//2+1,flush=True)
  if r!=n//2+1:
   import json
   open(__file__.replace('generate_probe.py','counterexample-probe.json'),'w').write(json.dumps(dict(n=n,edges=e,faces=faces,hcs=c,rank=r),indent=2)+'\n');break
 print('PROBES',total)
