"""Directed complete-graph box fibers: exact diagnostic, never a universal proof."""
import itertools,json,time
from collections import defaultdict
start=time.monotonic()
def counts(v,c):
 D={(0,)*(v-1):1}
 for i,j in itertools.combinations(range(v),2):
  d=tuple((int(k==i)-int(k==j)) for k in range(v-1)); E=defaultdict(int)
  for b,n in D.items():
   for t in range(c+1):E[tuple(x+t*y for x,y in zip(b,d))]+=n
  D=E
 return D
out=[]
for v,c in [(4,2),(5,1),(5,2),(5,3)]:
 D=counts(v,c);r=v-1
 # Directed triangular probes: primitive elementary coordinate and interval-root directions.
 U=[tuple(int(k==i)-int(k==j) for k in range(r)) for i in range(v) for j in range(v) if i!=j]
 directions=[(u,w) for u in U for w in U if u!=w and any(x+y for x,y in zip(u,w))]
 n=0;worst=None;hits=[]
 for b,z in D.items():
  for u,w in directions:
   a=tuple(x+y for x,y in zip(b,u));a2=tuple(x+y for x,y in zip(b,w));a3=tuple(x-y-t for x,y,t in zip(b,u,w))
   if a not in D or a2 not in D or a3 not in D:continue
   n+=1;lhs=z**3;rhs=D[a]*D[a2]*D[a3]
   if lhs<rhs:hits.append({'b':b,'points':[a,a2,a3],'counts':[z,D[a],D[a2],D[a3]]});break
  if hits:break
 out.append({'vertices':v,'capacity':c,'support':len(D),'triangles':n,'counterexamples':hits})
print(json.dumps({'networks':out,'seconds':time.monotonic()-start},indent=2))
