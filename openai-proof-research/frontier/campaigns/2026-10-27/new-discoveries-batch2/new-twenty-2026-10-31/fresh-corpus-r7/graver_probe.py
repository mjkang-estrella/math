from itertools import combinations_with_replacement,product,combinations
import time,json,os
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);start=time.monotonic();seen=0;skipped=0;witness=None
for A in combinations_with_replacement(range(1,6),3):
 for b in range(1,26):
  if time.monotonic()-start>40:break
  F=[(x,y,(b-A[0]*x-A[1]*y)//A[2]) for x in range(b//A[0]+1) for y in range(b//A[1]+1) if b-A[0]*x-A[1]*y>=0 and (b-A[0]*x-A[1]*y)%A[2]==0]
  if not 2<=len(F)<=60:skipped+=1;continue
  M=[[0]*len(F) for _ in F]
  for i,u in enumerate(F):
   for j in range(i):
    v=F[j]
    if not any(w!=u and w!=v and all(min(x,y)<=z<=max(x,y) for x,y,z in zip(u,v,w)) for w in F):M[i][j]=M[j][i]=1
  delta=min(map(sum,M));verts=list(range(len(F)));groups={i:{F[i]} for i in verts};cut=10**9;part=None
  while len(verts)>1:
   used=set();weights={i:0 for i in verts};prev=None
   for phase in range(len(verts)):
    x=max((i for i in verts if i not in used),key=lambda i:weights[i]);used.add(x)
    if phase==len(verts)-1:
     if weights[x]<cut:cut=weights[x];part=(groups[x].copy(),set(F)-groups[x])
     for v in verts:
      if v not in (prev,x):M[prev][v]+=M[x][v];M[v][prev]=M[prev][v]
     groups[prev]|=groups[x];verts.remove(x);break
    prev=x
    for v in verts:
     if v not in used:weights[v]+=M[x][v]
  seen+=1
  if cut<delta:witness=dict(A=A,b=b,F=F,delta=delta,cut=cut,partition=[list(x) for x in part]);break
 if witness or time.monotonic()-start>40:break
out=dict(checked_fibers=seen,skipped_size_or_trivial=skipped,elapsed=time.monotonic()-start,witness=witness,scope='positive one-row integer triples 1..5, rhs1..25, fibers size2..60; 40-second cutoff; no general theorem inferred',edge_test='u-v is Graver iff no third same-fiber point lies coordinatewise between u and v; any proper conformal kernel summand supplies precisely such a point')
Path(__file__).with_name('graver-diagnostics.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
