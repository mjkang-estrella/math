import pathlib,sys,itertools,json,random,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
D=pathlib.Path(__file__).resolve().parents[1];b=int(sys.argv[1]);rng=random.Random(101);done=[]
# n boundary vertices, pure cut entropies; choose representatives avoiding last boundary.
for interior in range(1,5):
 for rep in range(20):
  N=b+interior;edges=[(i,j) for i in range(N) for j in range(i+1,N) if rng.random()<.65];cap=np.array([rng.randint(1,9) for _ in edges],float);E=len(edges)
  cuts=[];mins=[];groups=[];ent=[]
  for S in range(1,1<<(b-1)):
   rows=[]
   for X in range(1<<interior):
    mask=S|(X<<b);rows.append(np.array([((mask>>i)^(mask>>j))&1 for i,j in edges],float))
   vals=[r@cap for r in rows];z=int(np.argmin(vals));mins.append(rows[z]);groups.append(rows);ent.append(vals[z])
  # n4 rays: Bell pairs, full4 perfect tensor. n5: Bell pairs and4perfect tensors for each omitted boundary.
  rays=[]
  for i,j in itertools.combinations(range(b),2):rays.append([int(((S>>i)^(S>>j))&1) for S in range(1,1<<(b-1))])
  fours=[tuple(range(4))] if b==4 else list(itertools.combinations(range(5),4))
  for F in fours:rays.append([min(sum(S>>i&1 for i in F),4-sum(S>>i&1 for i in F)) for S in range(1,1<<(b-1))])
  R=len(rays);V=R*(E+1);Aeq=[];beq=[];Aub=[]
  for e in range(E):
   r=np.zeros(V)
   for q in range(R):r[q*(E+1)+e]=1
   Aeq.append(r);beq.append(cap[e])
  for q,ray in enumerate(rays):
   off=q*(E+1)
   for s,(cut,rows) in enumerate(zip(mins,groups)):
    r=np.zeros(V);r[off:off+E]=cut;r[off+E]=-ray[s];Aeq.append(r);beq.append(0)
    for other in rows:
     r=np.zeros(V);r[off:off+E]=cut-other;Aub.append(r)
  res=linprog(np.zeros(V),A_eq=np.array(Aeq),b_eq=beq,A_ub=np.array(Aub),b_ub=np.zeros(len(Aub)),bounds=(0,None),method='highs',options={'time_limit':5,'threads':2})
  r={'boundaries':b,'interior':interior,'rep':rep,'status':res.status,'edges':edges,'capacities':list(map(int,cap)),'entropy':list(map(int,ent))};done.append(r)
  if res.status!=0:print('NONPASS',r,flush=True)
 print('completed',b,interior,'20 networks',flush=True)
(D/f'outputs/network{b}.json').write_text(json.dumps(done,indent=2)+'\n')
