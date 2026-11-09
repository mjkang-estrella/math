from pathlib import Path
from itertools import combinations
import random,json
L=Path(__file__).resolve().parent;r=random.Random(334146)
def refine(V,E):
 c={v:0 for v in V}
 for _ in range(len(V)):
  ks={v:(c[v],tuple(sorted(c[w] for w in V if tuple(sorted((v,w))) in E))) for v in V}
  palette={a:i for i,a in enumerate(sorted(set(ks.values())))};d={v:palette[ks[v]] for v in V}
  if len(set(d.values()))==len(V):return True
  if len(set(d.values()))==len(set(c.values())):return False
  c=d
 return False
tried=[]
for n in (12,14,16,18,20,24):
 for sample in range(20):
  E=frozenset(e for e in combinations(range(n),2) if r.randrange(2));passed=0
  for k in range(3):
   for S in combinations(range(n),k):
    if not refine([v for v in range(n) if v not in S],E):break
    passed+=1
   else:continue
   break
  tried.append({'n':n,'sample':sample,'passed_initial_deletions':passed})
  if passed==1+n+n*(n-1)//2:
   # connectedness
   seen={0}
   while True:
    nxt=seen|{w for a,b in E for v,w in ((a,b),(b,a)) if v in seen}
    if nxt==seen:break
    seen=nxt
   if len(seen)!=n:continue
   out={'n':n,'sample':sample,'edges':sorted(E),'deletion_sets_checked':passed,'method':'iterated degree refinement singleton partition for all deletions of size <=2','prior_trials':tried,'credit':'none; generic robust asymmetry mechanism, significance not established'}
   (L/'stability-results.json').write_text(json.dumps(out,indent=2));print(n,sample,passed);raise SystemExit
print('no robust singleton-refinement witness')
