from pathlib import Path
import random,itertools,json
L=Path(__file__).resolve().parents[1];random.seed(207)
def paths(n,E):
 a=[set() for _ in range(n)]
 for u,v in E:a[u].add(v);a[v].add(u)
 count=0
 for S in itertools.combinations(range(n),6):
  ds=sorted(len(a[v].intersection(S)) for v in S)
  if ds!=[1,1,2,2,2,2]:continue
  reached={S[0]};Q=[S[0]]
  for v in Q:
   for w in a[v].intersection(S):
    if w not in reached:reached.add(w);Q.append(w)
  count+=len(reached)==6
 return count
out=[]
for n in range(6,13):
 best=0;witness=None;tests=0
 seq=range(1<<15) if n==6 else range(1000)
 for i in seq:
  pairs=list(itertools.combinations(range(n),2));p=random.uniform(.15,.65)
  E=[e for k,e in enumerate(pairs) if (i>>k&1) if n==6] if n==6 else [e for e in pairs if random.random()<p]
  if not E:continue
  c=paths(n,E);r=c/len(E)**3;tests+=1
  if r>best:best=r;witness={'edges':E,'induced_p6':c,'edges_count':len(E),'ratio':r}
 if witness:witness['source_normalized_blowup_lower_bound']=best/4
 out.append({'n':n,'templates':tests,'complete_labeled_enumeration':n==6,'best':witness});print(n,tests,best,flush=True)
(L/'outputs/p6.json').write_text(json.dumps(out,indent=2))
