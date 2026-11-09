from pathlib import Path
import json,itertools,collections
from fractions import Fraction
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-review-r1');D=L.parent/'expanded-corpus-r198'
coords=[(i,) for i in range(5)]+list(itertools.combinations(range(5),2)); idx={c:i for i,c in enumerate(coords)}
good={sum(1<<i for i,c in enumerate(coords) if all(x>>v&1 for v in c)) for x in range(32)}
rows=json.loads((D/'outputs/submod-dual-compressed.json').read_text())['support'];balance=collections.Counter();checks=0
for perm in itertools.permutations(range(5)):
 pi=[idx[tuple(sorted(perm[v] for v in c))] for c in coords]
 def image(m):return sum(1<<pi[i] for i in range(15) if m>>i&1)
 assert {image(m) for m in good}==good
 for row in rows:
  w=row['weight'];assert isinstance(w,int) and w>0
  if row['kind']=='submodular':
   (a,ca),(b,cb),(x,cx),(y,cy)=row['terms'];assert [ca,cb,cx,cy]==[1,1,-1,-1]
   assert a==x&y and b==x|y
   assert image(a)==image(x)&image(y) and image(b)==image(x)|image(y)
   for m,c in row['terms']:balance[image(m)]+=w*c
   checks+=1
  else:
   m=row['point'];g=row['kind']=='good';assert (image(m) in good)==g
   balance[image(m)]+=w*(1 if g else -1)
assert all(c==0 for c in balance.values())
bound=-120*sum(r['weight'] for r in rows if r['kind']=='good');assert bound==-840
print('Exact expanded cancellation verified:',checks,'meet/join rows;',len(balance),'masks; bound',bound)
# Independent full-cube small-case LP; reconstruct rational solutions and check all local submodular inequalities exactly.
answers=[]
for d,r in [(2,2),(3,2),(3,3),(4,2)]:
 cs=[c for k in range(1,r+1) for c in itertools.combinations(range(d),k)];n=len(cs);N=1<<n
 p=D/f'outputs/submod-values-{d}-{r}.json'
 vals=[Fraction(str(v)).limit_denominator(1000000) for v in json.loads(p.read_text())];assert len(vals)==N
 G={sum(1<<i for i,c in enumerate(cs) if all(x>>v&1 for v in c)) for x in range(1<<d)}
 assert all(v<=-1 if m in G else v>=0 for m,v in enumerate(vals))
 count=0
 for i in range(n):
  for j in range(i+1,n):
   for m in range(N):
    if m>>i&1 or m>>j&1:continue
    assert vals[m]+vals[m|(1<<i)|(1<<j)]<=vals[m|1<<i]+vals[m|1<<j]
    count+=1
 C=max(0,-min(vals));answers.append({'d':d,'r':r,'local_inequalities_exact':count,'constant0_shift':str(C),'input':str(p)})
 print('Independent exact feasible-witness check',d,r,count,'rows; extend by C(1-z), C=',C)
(L/'math-receipt.json').write_text(json.dumps({'rows':13,'expanded_submodular_rows':checks,'balance_zero':True,'upper_bound':bound,'small_cases':answers},indent=2))
