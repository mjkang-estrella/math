import scipy.optimize as so,scipy.sparse as sp,numpy as np,itertools,json,pathlib,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def run(t,l,tri,seconds):
 n=2*t+2; dims=[n]*l+([3] if tri else []);verts=list(itertools.product(*[range(z) for z in dims]));idx={v:i for i,v in enumerate(verts)};edges=[]
 for i,v in enumerate(verts):
  for d,N in enumerate(dims):
   for x in range(v[d]+1,N):
    a,b=v[d],x
    adj=(d==l if tri else False) or b==n-1 or (b-a in (1,n-2))
    if adj:
     w=list(v);w[d]=x;edges.append((i,idx[tuple(w)]))
 rows=[];cols=[]
 for r,(a,b) in enumerate(edges):rows.extend([r,r]);cols.extend([a,b])
 A=sp.coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(len(edges),len(verts))).tocsc()
 if tri:weights=np.ones(len(verts))
 else:weights=np.array([2 if (v[0]==n-1)==(v[1]==n-1) else t+1 for v in verts])
 ts=time.monotonic();r=so.milp(-weights,integrality=np.ones(len(verts)),bounds=so.Bounds(0,1),constraints=so.LinearConstraint(A,-np.inf,1),options={'time_limit':seconds,'threads':2})
 row={'t':t,'ell':l,'triangle':tri,'status':r.status,'message':r.message,'wall':time.monotonic()-ts,'upper_bound':-float(r.mip_dual_bound) if r.get('mip_dual_bound') is not None else None}
 if r.x is not None:
  witness=[verts[i] for i,x in enumerate(r.x) if x>.5];S=set(witness)
  assert all(not(verts[a] in S and verts[b] in S) for a,b in edges)
  row.update(value=int(round(-r.fun)),witness=witness)
 if not tri:row['candidate_max']=2*(2*t*t+t+1)
 out.append(row);(D/'outputs/wheels.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in row.items() if k!='witness'},flush=True)
for t in range(2,13):run(t,2,False,4)
for t in [3,4,8,9]:run(t,2,True,5)
