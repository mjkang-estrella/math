from itertools import permutations,combinations
from collections import Counter
from functools import lru_cache
import json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def standard(v):return tuple(sorted(v).index(a) for a in v)
C={():Counter({0:1})};out=[]
for n in range(1,int(sys.argv[1])+1):
 top=tuple(reversed(range(n)))
 @lru_cache(None)
 def G(w):
  if w==top:return {tuple(range(n-1,-1,-1))+(0,):1}
  i=next(i for i in range(n-1) if w[i]<w[i+1]);v=list(w);v[i],v[i+1]=v[i+1],v[i];p=G(tuple(v));q=Counter()
  for e,c in p.items():
   for beta in (0,1):
    f=list(e);f[i+1]+=beta;f[-1]+=beta;a,b=f[i],f[i+1]
    if a>b:
     for j in range(a-b):
      t=f.copy();t[i]=a-1-j;t[i+1]=b+j;q[tuple(t)]+=c
    elif a<b:
     for j in range(b-a):
      t=f.copy();t[i]=b-1-j;t[i+1]=a+j;q[tuple(t)]-=c
  return {e:c for e,c in q.items() if c}
 bad=[];minimum=0;total=0
 for w in permutations(range(n)):
  p=Counter()
  for e,c in G(w).items():p[e[-1]]+=c
  for r in range(n):
   for ix in combinations(range(n),r):
    u=standard(tuple(w[i] for i in ix))
    for k,c in C[u].items():p[k]-=c
  p=Counter({k:c for k,c in p.items() if c});C[w]=p;total+=1
  if any(c<0 for c in p.values()):bad.append((w,dict(p)))
 rec={'n':n,'permutations_exhausted':total,'negative_coefficient_cases':bad,'nonzero_c_count':sum(bool(C[w]) for w in permutations(range(n))),'max_beta_degree':max((max(C[w],default=0) for w in permutations(range(n))),default=0)};out.append(rec);print(rec,flush=True)
 G.cache_clear()
(D/'outputs/groth.json').write_text(json.dumps(out,indent=2)+'\n')
(D/'outputs/groth-coefficients.json').write_text(json.dumps({','.join(str(i+1) for i in w):dict(p) for w,p in C.items()},indent=2)+'\n')
