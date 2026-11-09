from pathlib import Path
import sys,itertools,json,time
O=Path(__file__).resolve().parent; sys.path.insert(0,str(O/'deps')); import z3
for n in range(4,11):
 k=n-1; edges=list(itertools.combinations(range(n),2)); ts=list(itertools.combinations(range(n),3)); s=z3.Solver(); s.set(timeout=9000,max_memory=5000,threads=1); x={e:z3.Int('e%d_%d'%e) for e in edges}
 for i,e in enumerate(edges):
  s.add(x[e]>=0,x[e]<k)
  if i==0:s.add(x[e]==0)
  else:s.add(z3.Or(x[e]==0,*[x[e]<=x[f]+1 for f in edges[:i]]))
 masks=[]
 for t in ts:
  vals=[x[e] for e in itertools.combinations(t,2)]; masks.append(z3.Sum([z3.If(z3.Or(*[v==c for v in vals]),2**c,0) for c in range(k)]))
 s.add(z3.Distinct(masks)); start=time.monotonic(); res=s.check(); row={'n':n,'k':k,'result':str(res),'seconds':time.monotonic()-start}
 if res==z3.sat:
  m=s.model(); a={e:m.eval(x[e]).as_long() for e in edges}; sets=[frozenset(a[e] for e in itertools.combinations(t,2)) for t in ts]; assert len(set(sets))==len(ts); row['edges']=[[u,v,c] for (u,v),c in a.items()]
 elif res==z3.unknown:row['reason']=s.reason_unknown()
 print(json.dumps(row),flush=True)
