from pathlib import Path
import itertools,math,json,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
w=Path(__file__).resolve().parent;out=[];a=6
for c in [5,7]:
 prev=c-1
 while math.gcd(a,prev)!=1:prev-=1
 vertices=[x for x in itertools.product(range(a),repeat=a-1) if prev<sum(x)<=c];idx={x:i for i,x in enumerate(vertices)};adj=[]
 for x in vertices:
  neighbors=[]
  for k in range(a-1):
   y=list(x);y[k]+=1
   if k:y[k-1]-=1
   y=tuple(y)
   if y in idx:neighbors.append(idx[y])
  adj.append(neighbors)
 rank=[sum((i+1)*z for i,z in enumerate(x)) for x in vertices]
 from collections import Counter
 counts=Counter(rank); starts={}
 for k in range(max(rank)+1): starts[k]=counts[k]-sum(starts.get(k-j,0) for j in range(1,a))
 print('start-counts',c,starts,flush=True)
 paths=[]
 def walk(p):
  if len(p)==a:paths.append(tuple(p));return
  for j in adj[p[-1]]:walk(p+[j])
 for i in range(len(vertices)):
  if starts[rank[i]]>0:walk([i])
 print('generated',c,len(vertices),len(paths),flush=True)
 if len(paths)>500000:out.append(dict(c=c,status='path cap'));break
 row=[];col=[]
 for j,p in enumerate(paths):row+=list(p);col += [j]*a
 M=coo_matrix((np.ones(len(row)),(row,col)),shape=(len(vertices),len(paths))).tocsc()
 t=time.time();r=milp(np.zeros(len(paths)),integrality=np.ones(len(paths)),bounds=Bounds(0,1),constraints=LinearConstraint(M,1,1),options={'time_limit':25,'mip_rel_gap':0,'threads':2})
 d=dict(a=a,c=c,previous=prev,vertices=len(vertices),paths=len(paths),status=int(r.status),message=str(r.message),seconds=time.time()-t)
 if r.x is not None:
  chosen=[paths[j] for j,x in enumerate(r.x) if x>.5];flat=[v for p in chosen for v in p];valid=len(flat)==len(vertices) and len(set(flat))==len(vertices);d['independently_checked_partition']=valid
  if valid:(w/f'ribbon-pruned-a6-c{c}-witness.json').write_text(json.dumps([[vertices[i] for i in p] for p in chosen]))
 out.append(d);print(json.dumps(d),flush=True)
(w/'ribbon-pruned-output.json').write_text(json.dumps(out,indent=2))
