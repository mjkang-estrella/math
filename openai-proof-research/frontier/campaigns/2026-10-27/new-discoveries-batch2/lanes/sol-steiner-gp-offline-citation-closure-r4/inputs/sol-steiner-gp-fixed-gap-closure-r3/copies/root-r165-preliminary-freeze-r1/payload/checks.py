import json, random
from pathlib import Path
L=Path(__file__).resolve().parent
def tables(n,edges):
 adj=[0]*n
 for a,b in edges:adj[a]|=1<<b;adj[b]|=1<<a
 N=1<<n;cost=[n+1]*N;union=[0]*N
 for m in range(1,N):
  seen=m&-m;todo=seen
  while todo:
   q=todo&-todo;todo-=q;new=adj[q.bit_length()-1]&m&~seen;seen|=new;todo|=new
  if seen==m:cost[m]=m.bit_count();union[m]=m
 for m in range(N-1,0,-1):
  for v in range(n):
   if not (m>>v&1):
    t=m|1<<v
    if cost[t]<cost[m]:cost[m]=cost[t];union[m]=union[t]
    elif cost[t]==cost[m]:union[m]|=union[t]
 return cost,union
def good(A,k,U):
 B=A
 while B:
  if B.bit_count()==k and U[B]&A!=B:return False
  B=(B-1)&A
 return True
def values(n,edges):
 c,u=tables(n,edges);out=[]
 masks=sorted(range(1<<n),key=int.bit_count,reverse=True)
 for k in range(2,n):
  A=next(a for a in masks if good(a,k,u));out.append([k,A.bit_count(),A])
 return out
def run():
 out=[];rng=random.Random(165)
 # Explicit cycles, stars and complete graphs test the source-known formulas.
 for n in range(3,11):
  for name,e in [('cycle',[(i,(i+1)%n) for i in range(n)]),('star',[(0,i) for i in range(1,n)]),('complete',[(i,j) for i in range(n) for j in range(i+1,n)])]:
   v=values(n,e)
   for k,a,_ in v:
    expected=(max(n-1,k) if name=='star' else n if name=='complete' else k if (2*n)//3<=k<=n-2 else k+1)
    assert a==expected,(name,n,k,a,expected)
   out.append(dict(name=name,n=n,edges=e,values=v))
 for n in range(6,12):
  for t in range(12):
   # A fixed random spanning tree ensures connectedness; additional edges vary density.
   e={(i,rng.randrange(i)) for i in range(1,n)};e={tuple(sorted(x)) for x in e}
   p=[.12,.28,.48,.72][t%4]
   e|={(i,j) for i in range(n) for j in range(i+1,n) if rng.random()<p}
   e=sorted(e);v=values(n,e)
   out.append(dict(name='sample',n=n,edges=e,values=v))
 e=[(a,b) for a in range(6) for b in range(a+1,6) if abs(a//2-b//2)==1 or a//2==b//2]
 v=values(6,e);assert v[2][1]==5
 out.append(dict(name='P3_comp_K2',n=6,edges=e,values=v))
 decreases=[x for x in out if any(a[1]>b[1] for a,b in zip(x['values'],x['values'][1:]))]
 result=dict(records=out,decreases=decreases,scope='24 source controls, 72 seeded connected samples, one exact lexicographic example; no universal inference')
 (L/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
 print('graphs',len(out),'decreases',len(decreases),'product',v)
if __name__=='__main__':run()
