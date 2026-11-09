"""Bounded branch discovery, NOT certified arithmetic. No optimization sweep."""
import numpy as np,json,heapq,time
from pathlib import Path
p=Path(__file__).resolve().parent
A=np.load(p.parent/'fresh-corpus-r1/selected-packing-forms.npy')
T=np.zeros((7,6))
for i in range(1,7):T[i,:i]=1
B=np.einsum('ia,kij,jb->kab',T,A,T);B=(B+B.transpose(0,2,1))/2
# Deterministic candidates: source active forms plus maximizers on a coarse simplex lattice.
from itertools import combinations
ids=set([6901,7223,11927,12088,16862,16932,19284,19354])
for bars in combinations(range(10),5):
 z=np.diff([-1,*bars,10])-1;g=z/5
 ids.add(int(np.argmax(np.einsum('i,kij,j->k',g,B,g))))
ids=sorted(ids);B=B[ids];print('forms',len(ids),flush=True)
c=.6471;start=time.monotonic();serial=0
# symmetric quadratic Bernstein coefficients on each simplex = vi^T B vj (cross terms).
def bound(V):return float(np.max(np.min(np.einsum('ai,kij,bj->kab',V,B,V),axis=(1,2))))
V=np.eye(6);heap=[(bound(V),serial,V,0)];done=0;maxdepth=0;best=(2,None);counts={}
while heap and done<500000 and time.monotonic()-start<55:
 lb,_,V,depth=heapq.heappop(heap)
 if lb>=c: continue
 center=V.mean(axis=0); val=float(np.max(np.einsum('i,kij,j->k',center,B,center)))
 if val<best[0]:best=(val,center.tolist())
 if val<c-1e-9:
  print('potential separator failure',best,flush=True);break
 dist=np.sum((V[:,None,:]-V[None,:,:])**2,axis=2);i,j=np.unravel_index(np.argmax(dist),dist.shape)
 for k in [i,j]:
  W=V.copy();W[k]=(V[i]+V[j])/2;w=bound(W);serial+=1
  if w<c:heapq.heappush(heap,(w,serial,W,depth+1))
 done+=1;maxdepth=max(maxdepth,depth)
 if done%2500==0:print(done,'queue',len(heap),'lb',heap[0][0] if heap else c,'best',best[0],flush=True)
out=dict(scope='floating Bernstein discovery only; no certificate',selected_form_ids=ids,processed=done,queue=len(heap),maxdepth=maxdepth,best_center=best,remaining_lower_bound=heap[0][0] if heap else c,elapsed_seconds=time.monotonic()-start,closed=not heap)
(p/'symmetric-branch-extended.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
