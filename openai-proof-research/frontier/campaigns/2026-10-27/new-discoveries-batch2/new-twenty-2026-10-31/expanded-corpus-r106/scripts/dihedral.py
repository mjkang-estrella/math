from itertools import combinations
import json
bad={tuple(map(int,s)) for s in '3142 1342 2314 2134 3241 4231 3421 4213 2413 1324 3124 1423 2431 4312 4132 1243'.split()}
def patt(x):return tuple(sorted(x).index(v)+1 for v in x)
perms={()};out=[]
for n in range(1,21):
 nxt=set()
 for p in perms:
  for j in range(n):
   q=p[:j]+(n,)+p[j:]
   if all(patt([q[t] for t in idx]) not in bad for idx in combinations(range(n),4) if j in idx):nxt.add(q)
 expected=set()
 for p in [tuple(range(1,n+1)),tuple(range(n,0,-1))]:
  expected|={p[j:]+p[:j] for j in range(n)}
 out.append({'n':n,'count':len(nxt),'missing':len(expected-nxt),'extra':len(nxt-expected)});perms=nxt
 print(out[-1],flush=True)
open('outputs/dihedral.json','w').write(json.dumps(out,indent=2))
