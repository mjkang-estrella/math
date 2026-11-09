"""Finite exact diagnostics only, not an unrestricted extremal proof."""
import itertools,json

def diamonds(F):
 s=set(F)
 return sum(a|b in s and a&b in s for a,b in itertools.combinations(s,2) if (a&b)!=a and (a&b)!=b)
def shift(F,i):
 s=set(F); bit=1<<i
 return {a^bit if a&bit and a^bit not in s else a for a in s}
out={'model':'ambient union/intersection, not induced-poset copies','exhaustive':[],'compression_failure':None}
for m in [4,8]:
 best=-1;w=None;total=0
 for F in itertools.combinations(range(16),m):
  v=diamonds(F);total+=1
  if v>best:best=v;w=F
  if out['compression_failure'] is None:
   for i in range(4):
    G=shift(F,i);b=diamonds(G)
    if b<v:out['compression_failure']=dict(F=F,coordinate=i,before=v,after=b,shifted=sorted(G));break
 out['exhaustive'].append(dict(universe_size=4,family_size=m,families=total,maximum=best,witness=w))
out['boolean_values']={str(n):diamonds(range(1<<n)) for n in range(2,7)}
open('boolean-diagnostic.json','w').write(json.dumps(out,indent=2));print(out)
