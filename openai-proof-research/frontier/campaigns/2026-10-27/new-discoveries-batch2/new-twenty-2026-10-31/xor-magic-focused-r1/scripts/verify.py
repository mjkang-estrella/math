import json,itertools
from pathlib import Path
from functools import reduce
from operator import xor
def verify(g):
 N=g['N'];d=g['d'];closed=g['closed'];E=list(map(tuple,g['edges']));assert N>=4 and N&(N-1)==0;assert len(E)==len(set(E));assert all(0<=u<v<N for u,v in E)
 adj=[set() for _ in range(N)]
 for u,v in E:adj[u].add(v);adj[v].add(u)
 assert all(len(a)==d for a in adj)
 assert all(reduce(xor,adj[u],u if closed else 0)==0 for u in range(N))
 R={0};Q=[0]
 for u in Q:
  for v in adj[u]-R:R.add(v);Q.append(v)
 assert len(R)==N
 return dict(N=N,d=d,closed=closed,simple=True,regular=True,connected=True,identity_labels_bijective=True,zero_xor=True)
def complement(g):
 N=g['N'];return dict(N=N,d=N-1-g['d'],closed=not g['closed'],edges=sorted(set(itertools.combinations(range(N),2))-set(map(tuple,g['edges']))))
if __name__=='__main__':
 out=[]
 for p in Path('outputs').glob('*.json'):
  g=json.loads(p.read_text())
  if 'edges' not in g or 'N' not in g:continue
  if 'closed' not in g:g['closed']=False
  out.append(dict(file=str(p),**verify(g)));out.append(dict(file=str(p),complement=True,**verify(complement(g))))
 Path('outputs/exact-verification.json').write_text(json.dumps(out,indent=2));print(out)
