"""Independent integer augmenting-path checks of the two diagnostic cut models."""
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import random,json
from pathlib import Path

def augment(n,edges,caps,s,t):
 r=[[0]*n for _ in range(n)]
 for (a,b),c in zip(edges,caps):r[a][b]+=c;r[b][a]+=c
 ans=0
 while True:
  par={s:None};todo=[s]
  for a in todo:
   for b in range(n):
    if b not in par and r[a][b]>0:par[b]=a;todo.append(b)
  if t not in par:return ans
  z=t;d=10**9
  while z!=s:d=min(d,r[par[z]][z]);z=par[z]
  z=t
  while z!=s:a=par[z];r[a][z]-=d;r[z][a]+=d;z=a
  ans+=d

def main():
 rng=random.Random(20261029);cases=0
 for n,s,t,edges in [(4,0,3,[(0,1),(0,2),(1,3),(2,3),(1,2)]),(5,0,4,[(0,i) for i in [1,2,3]]+[(i,4) for i in [1,2,3]]+[(1,2),(1,3),(2,3)])]:
  others=[i for i in range(n) if i not in [s,t]]
  for _ in range(300):
   cs=[rng.randrange(21) for e in edges]
   def cutflow(c):
    return min(sum(c[j] for j,(a,b) in enumerate(edges) if (a in side)!=(b in side)) for mask in range(1<<len(others)) for side in [{s}|{v for i,v in enumerate(others) if mask>>i&1}])
   f=augment(n,edges,cs,s,t);assert f==cutflow(cs)
   if n==4:
    a,b,c,d,e=cs;assert f==min(a+b,c+d,a+d+e,b+c+e)
   for k in [1,2,3,4,10]:assert (f>=k)==(cutflow([min(c,k) for c in cs])>=k)
   cases+=1
 out={'status':'PASS','integer_configurations':cases,'clip_threshold_checks':cases*5,'method':'independent residual augmentations vs cut enumeration; deterministic seed; no universal numeric proof'}
 (Path(__file__).resolve().parent/'cut-validation.json').write_text(json.dumps(out,indent=2));print(out)
if __name__=='__main__':main()
