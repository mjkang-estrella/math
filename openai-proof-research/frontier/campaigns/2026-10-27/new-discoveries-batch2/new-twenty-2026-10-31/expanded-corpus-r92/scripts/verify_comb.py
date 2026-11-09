from pathlib import Path
import json,collections
D=Path(__file__).resolve().parents[1];V=[(x,y) for x in range(3) for y in range(36)]
def adj(v):
 x,y=v
 return [w for w in V if (w[0]==x and abs(w[1]-y)==1) or (y==w[1]==0 and abs(w[0]-x)==1)]
A={v:adj(v) for v in V}
def ball(v,r):
 s={v}
 for _ in range(r):s|={w for u in s for w in A[u]}
 return s
cs=json.load(open(D/'outputs/comb-witness.json'))['centers'];cs=list(map(tuple,cs));burned=set();stages=[]
for t,c in enumerate(cs):
 before=burned|{w for u in burned for w in A[u]}
 assert c not in before
 burned=before|{c};stages.append(len(burned))
assert len(burned)==108
allrows=[]
for T in range(1,12):
 for S in range(3):
  rem=set(V)-ball((S,0),T-1);trace=[]
  # Graph Algorithm 2 applicable only once all spine vertices are removed.
  if any(y==0 for x,y in rem):allrows.append(dict(T=T,S=S,spine_uncovered=True,success=False));continue
  lengths=[sum(x==i for x,y in rem) for i in range(3)]
  for r in range(T-2,-1,-1):
   # longest remaining path, tie leftmost; burning confined to that component
   i=max(range(3),key=lambda x:sum(v[0]==x for v in rem));path=sorted(v for v in rem if v[0]==i)
   if not path:break
   center=path[min(r,len(path)-1)];rem-={v for v in path if abs(v[1]-center[1])<=r};trace.append(dict(r=r,center=center,left=len(rem)))
  allrows.append(dict(T=T,S=S,lengths=lengths,trace=trace,remaining=sorted(rem),success=not rem))
assert not any(z['success'] for z in allrows if z['T']<=10)
assert all(z['success'] for z in allrows if z['T']==11)
res={'burning_stages':stages,'centers':cs,'greedy':allrows};(D/'outputs/comb-independent.json').write_text(json.dumps(res,indent=2));print('BFS verified burning:',stages,'; greedy fails for every T<=10 and S; succeeds at11')
