from itertools import product, combinations
from math import isqrt
from pathlib import Path
import json
out={}
for name,A in [('positive',[1,2,4,8,16]),('zero',[0,2,3,5,7])]:
 reps={}
 for a,b,c,d in product(A,repeat=4):
  s,D=a+d,(a-d)**2+4*b*c
  t=isqrt(D)
  key=(s+t,0) if t*t==D else (s,D)
  reps.setdefault(key,[]).append([a,b,c,d])
 failures=[]
 for (s,D),(t,E) in combinations(reps,2):
  separated=(D!=E) if s==t else ((D-E-(t-s)**2)**2!=4*(t-s)**2*E)
  if not separated: failures.append([[s,D],[t,E]])
 out[name]={'alphabet':A,'tuples':sum(map(len,reps.values())),'keys':len(reps),'unordered_pairs':len(reps)*(len(reps)-1)//2,'failed_necessary_equation_separations':failures,'representatives':[{ 'key':k,'tuple':v[0],'multiplicity':len(v)} for k,v in sorted(reps.items())]}
Path('diagnostic-review.json').write_text(json.dumps(out,indent=2))
print({k:{x:y for x,y in v.items() if x!='representatives'} for k,v in out.items()})
