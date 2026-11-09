# Equal-size one-step lemma via type-level max flow: comps(u,B)xcomps(v,B) -> comps(u+1,B)xcomps(v-1,B), u+2<=v.
import sys
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth import parts_count, combine, maxflow_ok
Bm=int(sys.argv[1]); nmax=int(sys.argv[2])
cnt=0;bad=0
for B in range(1,Bm+1):
  for n in range(2,nmax+1):
    for u in range(0,n):
      v=n-u
      if u+2>v: break
      X=combine(parts_count(u,B),parts_count(v,B)); Y=combine(parts_count(u+1,B),parts_count(v-1,B))
      f=maxflow_ok(X,Y); nx=sum(X.values()); cnt+=1
      if f<nx: bad+=1; print('FAIL B',B,'u',u,'v',v,nx,f,flush=True)
print('cases',cnt,'fail',bad)
