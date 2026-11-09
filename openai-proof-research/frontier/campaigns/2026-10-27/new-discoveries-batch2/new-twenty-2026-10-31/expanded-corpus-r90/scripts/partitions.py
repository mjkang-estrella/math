from pathlib import Path
from collections import Counter
from functools import lru_cache
import json
@lru_cache(None)
def parts(n,m,distinct,odd):
 if n==0:return ((),)
 return tuple((k,)+p for k in range(min(n,m),0,-1) if not odd or k%2 for p in parts(n-k,k-1 if distinct else k,distinct,odd))
def hooks(p):return Counter(p[i]-j+sum(q>j for q in p[i+1:]) for i in range(len(p)) for j in range(p[i]))
rows=[];N=[0,0,0,7,8,18,16,34,34,56,59]
for n in range(61):
 totals=[]
 for distinct,odd in [(False,True),(True,False)]:
  c=Counter()
  for p in parts(n,n,distinct,odd):c.update(hooks(p))
  totals.append(c)
 dif={t:totals[0][t]-totals[1][t] for t in range(2,11)};rows.append({'n':n,'difference':dif,'violations':[t for t in dif if n>N[t] and dif[t]<0]})
 print(n,rows[-1],flush=True)
Path('outputs/hooks.json').write_text(json.dumps(rows,indent=2)+'\n')
