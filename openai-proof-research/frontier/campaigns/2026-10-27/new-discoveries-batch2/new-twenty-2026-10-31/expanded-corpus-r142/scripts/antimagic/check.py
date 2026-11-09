# Independent checker: bijection onto [1,m], proper (adjacent vertex sums differ), #colours = l+1.
import sys,json,importlib.util,time
spec=importlib.util.spec_from_file_location('construct',sys.argv[1]); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
out=[]
for arg in sys.argv[2:]:
  t,n=map(int,arg.split(','))
  t0=time.time(); rows,par,lab=mod.construct(t,n)
  V=len(par); m=V-1
  # independent shape check: complete full t-ary tree with n levels
  depth=[0]*V; kids=[0]*V
  for v in range(1,V):
    assert 0<=par[v]<v; depth[v]=depth[par[v]]+1; kids[par[v]]+=1
  assert all((kids[v]==t and depth[v]<n) or (kids[v]==0 and depth[v]==n) for v in range(V)), 'shape'
  assert V==sum(t**h for h in range(n+1))
  assert set(lab)==set(range(1,V)), 'every non-root vertex has a parent edge label'
  assert sorted(lab.values())==list(range(1,m+1)), 'bijection'
  w=[0]*V
  for v in range(1,V): w[v]+=lab[v]; w[par[v]]+=lab[v]
  proper=all(w[v]!=w[par[v]] for v in range(1,V))
  leaves=[v for v in range(V) if v not in set(par[1:])]
  ncol=len(set(w))
  out.append(dict(t=t,n=n,edges=m,leaves=len(leaves),proper=proper,colours=ncol,ok=proper and ncol==len(leaves)+1,secs=round(time.time()-t0,2)))
  print(json.dumps(out[-1]),flush=True)
