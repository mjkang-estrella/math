import numpy as np,random,itertools,time,json,pathlib
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import csc_matrix
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(138);out=[]
# Triangle-free 13-vertex circulant with independence number4. Verify literally.
H={(u,v) for u in range(13) for v in range(u+1,13) if (v-u)%13 in [1,5,8,12]}
assert all(any((u,v) not in H for u,v in itertools.combinations(S,2)) for S in itertools.combinations(range(13),3))
assert all(any((u,v) in H for u,v in itertools.combinations(S,2)) for S in itertools.combinations(range(13),5))
for n in range(9,14):
 tested=drawn=0;start=time.monotonic()
 while tested<16 and drawn<500:
  drawn+=1;verts=rng.sample(range(13),n);U=[(u,v) for u,v in itertools.combinations(range(n),2) if tuple(sorted((verts[u],verts[v]))) not in H]
  assert all(any((u,v) in U for u,v in itertools.combinations(S,2)) for S in itertools.combinations(range(n),3))
  assert all(any((u,v) not in U for u,v in itertools.combinations(S,2)) for S in itertools.combinations(range(n),5))
  E=[];digons=0
  for u,v in U:
   z=rng.randrange(3)
   if z!=0:E.append((u,v))
   if z!=1:E.append((v,u))
   if z==2:digons+=1
  if not digons:continue
  m=len(E);leaves=[];cross=[];ok=True
  for S in range(1,(1<<n)-1):
   le=[j for j,(u,v) in enumerate(E) if S>>u&1 and not S>>v&1]
   if len(le)<2:ok=False;break
   leaves.append(le);cross.append([j for j,(u,v) in enumerate(E) if (S>>u&1)!=(S>>v&1)])
  if not ok:continue
  tested+=1;rows=[];cols=[];vals=[];lb=[];ub=[]
  def row(js,l,u):
   i=len(lb);lb.append(l);ub.append(u)
   for j in js:rows.append(i);cols.append(j);vals.append(1.)
  row(range(m),n-1,n-1)
  for le,cr in zip(leaves,cross):row(le,0,len(le)-1);row(cr,1,np.inf)
  mat=csc_matrix((vals,(rows,cols)),shape=(len(lb),m))
  res=milp(np.zeros(m),integrality=np.ones(m),bounds=Bounds(0,1),constraints=LinearConstraint(mat,lb,ub),options={'time_limit':2,'threads':1})
  rec=dict(n=n,drawn=drawn,sample=tested,arcs_literal=E,status=int(res.status),min_directed_cut=min(map(len,leaves)),digons=digons,underlying_clique_upper_bound=4,alpha_upper_bound=2)
  if res.status==0:
   T=[E[j] for j,x in enumerate(res.x) if x>.5];rec['tree']=T;assert len(T)==n-1
   rem=set(E)-set(T)
   assert all(any((u,v) in rem for u,v in E if S>>u&1 and not S>>v&1) for S in range(1,(1<<n)-1))
   seen={0}
   while True:
    old=len(seen)
    for u,v in T:
     if u in seen or v in seen:seen.update([u,v])
    if len(seen)==old:break
   assert len(seen)==n
  out.append(rec);(D/'outputs/digraph-ramsey.json').write_text(json.dumps(out,indent=2)+'\n');print(n,tested,res.status,flush=True)
  if res.status==2:print('INFEASIBLE CANDIDATE',rec,flush=True);raise SystemExit
 print('END',n,'drawn',drawn,'tested',tested,'seconds',time.monotonic()-start,flush=True)
