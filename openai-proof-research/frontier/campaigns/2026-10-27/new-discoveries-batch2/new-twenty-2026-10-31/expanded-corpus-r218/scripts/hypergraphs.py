from pathlib import Path
from itertools import combinations
from math import comb
from fractions import Fraction
import random,json
D=Path(__file__).resolve().parents[1];rows=[];rng=random.Random(218)
for n,r,sampling in [(5,3,False),(6,3,True)]:
 es=[sum(1<<v for v in t) for t in combinations(range(n),r)];eligible=0;checked=0;bad=[]
 codes=range(1,1<<len(es)) if not sampling else [rng.randrange(1,1<<len(es)) for _ in range(20000)]
 for code in codes:
  edges=[e for j,e in enumerate(es) if code>>j&1];checked+=1
  levels=[];s=None
  for m in range(r+1):
   subs=[sum(1<<v for v in t) for t in combinations(range(n),m)];inc=[sum(1<<j for j,e in enumerate(edges) if e&t==t) for t in subs];inc=[x for x in inc if x]
   levels.append(inc)
   if any(x.bit_count()==1 for x in inc):s=m;break
  if s is None or s<2 or(sampling and s!=2):continue
  inc=levels[s-1];delta=min(x.bit_count() for x in inc);ks=[k for k in range(r+1,20) if comb(k-s+1,r-s+1)==delta]
  if not ks:continue
  eligible+=1;bound=Fraction(delta,comb(r,s-1))-Fraction(1,comb(ks[0],s-1));b=len(inc);lim=b-comb(r,s-1);gamma=None
  union=[0]*(1<<b)
  for mask in range(1,1<<b):
   j=(mask&-mask).bit_length()-1;union[mask]=union[mask^(1<<j)]|inc[j];sz=mask.bit_count()
   if sz>lim:continue
   f=Fraction(union[mask].bit_count()-1,sz)
   if gamma is None or f<gamma:gamma=f
  if gamma is not None and gamma<bound:bad.append({'n':n,'edges':edges,'s':s,'delta':delta,'gamma':str(gamma),'bound':str(bound)})
 row={'n':n,'r':r,'sampling':sampling,'seed':218 if sampling else None,'checked':checked,'eligible':eligible,'violations':bad};rows.append(row);print(json.dumps(row),flush=True)
 (D/'logs/hypergraphs-results.json').write_text(json.dumps(rows,indent=2))
