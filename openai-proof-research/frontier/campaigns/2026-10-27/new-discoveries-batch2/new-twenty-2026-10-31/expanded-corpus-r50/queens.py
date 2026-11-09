import resource
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(55,55))
import numpy as np,itertools,json,pathlib,scipy.optimize as so,scipy.sparse as sp
p=pathlib.Path(__file__).resolve().parent;points=np.array(list(itertools.product(range(4),repeat=5)));pairs=[]
for i,x in enumerate(points):
 dif=np.abs(points[i+1:]-x);nonzero=np.max(dif,axis=1);hit=np.all((dif==0)|(dif==nonzero[:,None]),axis=1)
 pairs.extend((i,i+1+int(j)) for j in np.flatnonzero(hit))
rows=[];cols=[]
for r,(i,j) in enumerate(pairs):rows.extend([r,r]);cols.extend([i,j])
last=len(pairs);rows.extend([last]*1024);cols.extend(range(1024));A=sp.csc_array((np.ones(len(rows)),(rows,cols)),shape=(last+1,1024));low=np.full(last+1,-np.inf);up=np.ones(last+1);low[-1]=up[-1]=32
print('vars1024 attackpairconstraints',last,flush=True)
r=so.milp(np.zeros(1024),integrality=np.ones(1024),bounds=so.Bounds(0,1),constraints=so.LinearConstraint(A,low,up),options={'time_limit':22,'threads':1,'disp':True});print(r,flush=True)
if r.x is not None:
 ids=np.flatnonzero(r.x>.5);S=points[ids];assert len(S)==32
 for i,x in enumerate(S):
  for y in S[i+1:]:assert len(set(abs(int(a)-int(b)) for a,b in zip(x,y))-{0})>=2
 (p/'queens5-witness.json').write_text(json.dumps(S.tolist()));print('CHECKED32',S.tolist())
