import itertools,time,json
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix,vstack,csr_matrix
from pathlib import Path
D=Path(__file__).resolve().parents[1];records=[]
def objects(n):
 out=[]
 def rec(p,free):
  if not free:
   if sum(x<0 for x in p)%2==0:out.append(tuple(p))
   return
  i=free[0]
  for s in [1,-1]:p[i]=s*(i+1);rec(p,free[1:])
  for j in free[1:]:
   for s in [1,-1]:p[i]=s*(j+1);p[j]=s*(i+1);rec(p,[x for x in free if x!=i and x!=j])
 rec([0]*n,list(range(n)));return out
for n in [4,5,6]:
 V=objects(n);N=len(V);E=[(i,j) for i in range(N) for j in range(i) if sum(x!=y for x,y in zip(V[i],V[j]))==2];A=lil_matrix((N,len(E)))
 for e,(i,j) in enumerate(E):A[i,e]=A[j,e]=1
 constraints=[LinearConstraint(A.tocsr(),2,2)];rng=np.random.default_rng(115);start=time.monotonic();rounds=0;cycle=None;last=None
 while time.monotonic()-start<32:
  res=milp(rng.random(len(E)),integrality=np.ones(len(E)),bounds=Bounds(0,1),constraints=constraints,options={'time_limit':max(1,32-(time.monotonic()-start)),'threads':2});rounds+=1;last=res.message
  if res.x is None:break
  adj=[[] for _ in V]
  for e,(i,j) in enumerate(E):
   if res.x[e]>.5:adj[i].append(j);adj[j].append(i)
  unseen=set(range(N));components=[]
  while unseen:
   c=[];stack=[next(iter(unseen))];unseen.remove(stack[0])
   while stack:
    i=stack.pop();c.append(i)
    for j in adj[i]:
     if j in unseen:unseen.remove(j);stack.append(j)
   components.append(c)
  if len(components)==1:
   cycle=[0];prev=-1;cur=0
   while True:
    nxt=next(j for j in adj[cur] if j!=prev)
    if nxt==0:break
    cycle.append(nxt);prev,cur=cur,nxt
   assert len(cycle)==N;break
  cuts=lil_matrix((len(components),len(E)))
  for t,c in enumerate(components):
   S=set(c)
   for e,(i,j) in enumerate(E):
    if (i in S)!=(j in S):cuts[t,e]=1
  constraints.append(LinearConstraint(cuts.tocsr(),2,np.inf))
 row=dict(n=n,vertices=N,edges=len(E),milp_rounds=rounds,hamilton_cycle_found=cycle is not None,last_message=last,cycle=[V[i] for i in cycle] if cycle else None);records.append(row);print({k:v for k,v in row.items() if k!='cycle'},flush=True)
 (D/'outputs/involutions.json').write_text(json.dumps(records,indent=2)+'\n')
