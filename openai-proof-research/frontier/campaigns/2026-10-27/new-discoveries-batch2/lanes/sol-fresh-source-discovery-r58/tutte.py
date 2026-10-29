from math import comb
from check import P,poly
import json
m=n=3;N=m+n;rank=N-1;out=[0]*(m*n+rank+1)
edges=[(i,m+j) for i in range(m) for j in range(n)]
for mask in range(1<<len(edges)):
 parent=list(range(N))
 def root(i):
  while parent[i]!=i:i=parent[i]
  return i
 size=mask.bit_count()
 for t,(i,j) in enumerate(edges):
  if (mask>>t)&1:parent[root(i)]=root(j)
 ra=N-len({root(i) for i in range(N)})
 for j in range(rank-ra+1):out[size+j]+=(-1)**j*comb(rank-ra,j)
while out[-1]==0:out.pop()
a,_=poly(3,3);assert a!=out
v=dict(lacking=a,stella_tutte_specialization=out)
print(v);(P/'tutte.json').write_text(json.dumps(v,indent=2)+'\n')
