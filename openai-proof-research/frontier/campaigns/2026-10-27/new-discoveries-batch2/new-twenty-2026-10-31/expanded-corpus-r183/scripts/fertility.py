from pathlib import Path
from itertools import permutations
from collections import Counter
import json
D=Path(__file__).resolve().parents[1];patterns=list(permutations(range(3)));out=[]
def sc(pi,sigma):
 stack=[];ans=[];j=0
 while j<len(pi):
  x=pi[j]
  triple=[x]+stack[-2:][::-1]
  pat=tuple(sorted(triple).index(v) for v in triple)
  if len(stack)>=2 and pat==sigma:ans.append(stack.pop())
  else:stack.append(x);j+=1
 return tuple(ans+stack[::-1])
for sigma in patterns:
 observed=set();rows=[]
 for n in range(1,9):
  count=Counter(sc(pi,sigma) for pi in permutations(range(n)));values=set(count.values());observed|=values
  rows.append({'n':n,'images':len(count),'max_fertility':max(values),'fertility_values':sorted(values)})
 missing=next(x for x in range(1,max(observed)+2) if x not in observed)
 out.append({'sigma':sigma,'sizes':rows,'first_unobserved_positive_fertility_through_n8':missing});print(sigma,'first unobserved',missing,flush=True)
(D/'outputs/fertility.json').write_text(json.dumps(out,indent=2)+'\n')
