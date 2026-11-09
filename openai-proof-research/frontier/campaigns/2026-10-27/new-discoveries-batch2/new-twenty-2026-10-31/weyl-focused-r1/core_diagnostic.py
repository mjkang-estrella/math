"""Bounded exact integer diagnostic, not a proof or Lean certificate.
Cap 2000 chambers; no E6/E7/E8 group enumeration.
"""
from itertools import product, combinations
from collections import deque,Counter
import json,time
from pathlib import Path

def roots(kind,n):
 out=set()
 def put(v):out.add(tuple(v))
 if kind in ('B','C','D','F'):
  for i,j in combinations(range(n),2):
   for s,t in product((-2,2),repeat=2):
    v=[0]*n;v[i]=s;v[j]=t;put(v)
  if kind!='D':
   for i in range(n):
    for s in (-2,2):
     v=[0]*n;v[i]=s*(2 if kind=='C' else 1);put(v)
  if kind=='F':
   out.update(product((-1,1),repeat=4))
 if kind=='G':
  for i,j in combinations(range(3),2):
   v=[0]*3;v[i]=1;v[j]=-1;put(v);put([-x for x in v])
  for i in range(3):
   v=[-1]*3;v[i]=2;put(v);put([-x for x in v])
 return sorted(out)

def run(kind,n):
 R=roots(kind,n); ix={r:i for i,r in enumerate(R)};m=len(R)
 dot=lambda a,b:sum(x*y for x,y in zip(a,b))
 pos=[i for i,r in enumerate(R) if dot(r,[100**k for k in range(len(r))])>0]
 simple=[i for i in pos if not any(tuple(x-y for x,y in zip(R[i],R[j])) in ix and ix[tuple(x-y for x,y in zip(R[i],R[j]))] in pos for j in pos)]
 def refl(a,b):
  d=dot(b,b);t=2*dot(a,b)
  assert all((x*d-t*y)%d==0 for x,y in zip(a,b))
  return tuple((x*d-t*y)//d for x,y in zip(a,b))
 gens=[tuple(ix[refl(r,R[s])] for r in R) for s in simple]
 identity=tuple(range(m));W=[identity];known={identity};queue=deque([identity])
 while queue:
  p=queue.popleft()
  for g in gens:
   q=tuple(p[g[i]] for i in range(m))
   if q not in known:
    known.add(q);W.append(q);queue.append(q)
    assert len(W)<=2000,'chamber cap'
 base=sum(1<<i for i in pos); core=[i for i in pos if i not in simple]
 cores=[sum(1<<w[i] for i in core) for w in W]
 def witness(d):return next((i for i,c in enumerate(cores) if d&~c==0),None)
 S=[];witnesses=[]
 for w in W:
  b=sum(1<<w[i] for i in pos);k=witness(base&~b)
  if w!=identity and k is not None:S.append(w);witnesses.append(k)
 dist={identity:0};queue=deque([identity])
 while queue:
  p=queue.popleft()
  for g in S:
   q=tuple(p[g[i]] for i in range(m))
   if q not in dist:dist[q]=dist[p]+1;queue.append(q)
 return dict(type=kind+str(n),roots=m,vertices=len(W),generators=len(S),histogram=dict(Counter(dist.values())),complete=len(dist)==len(W),diameter=max(dist.values()))
if __name__=='__main__':
 out=[]
 for k,n in [('B',2),('B',3),('B',4),('C',3),('D',4),('F',4),('G',2)]:
  t=time.time();r=run(k,n);r['seconds']=time.time()-t;out.append(r);print(r,flush=True)
 Path(__file__).with_name('core-diagnostic.json').write_text(json.dumps(out,indent=2))
