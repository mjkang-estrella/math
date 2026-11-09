from pathlib import Path
from itertools import product
from fractions import Fraction
from functools import lru_cache
import random,json
L=Path(__file__).resolve().parent; rng=random.Random(334438)
def hist(n,E,q):
 H=[0]*(len(E)+1)
 # Fix first colour at zero, restoring factor q afterwards.
 for rest in product(range(q),repeat=n-1):
  c=(0,)+rest;H[sum(c[a]==c[b] for a,b in E)]+=q
 return H
@lru_cache(None)
def ref(d,q,bip):
 n=2*d if bip else d+1;E=[(i,j) for i in range(n) for j in range(i+1,n) if not bip or (i<d<=j)]
 return n,hist(n,E,q)
def energy(n,H,x):
 s=sum(Fraction(h)*x**i for i,h in enumerate(H));return sum(Fraction(i*h)*x**i for i,h in enumerate(H))/(n*s)
rows=[]
for n in (8,10,12):
 for d in (4,5):
  if d>=n:continue
  E=set()
  for i in range(n):
   for s in range(1,d//2+1):E.add(tuple(sorted((i,(i+s)%n))))
   if d%2:E.add(tuple(sorted((i,(i+n//2)%n))))
  assert all(sum(v in e for e in E)==d for v in range(n))
  for sample in range(6):
   if sample:
    for _ in range(100):
     (a,b),(c,f)=rng.sample(sorted(E),2)
     if rng.randrange(2):a,b=b,a
     if len({a,b,c,f})<4:continue
     x=tuple(sorted((a,c)));y=tuple(sorted((b,f)))
     if x in E or y in E:continue
     E.remove(tuple(sorted((a,b))));E.remove(tuple(sorted((c,f))));E.update((x,y))
   for q in (2,3):
    H=hist(n,sorted(E),q);fail=[]
    for x in (Fraction(1,8),Fraction(1,4),Fraction(1,2),Fraction(3,4),Fraction(7,8)):
     u=energy(n,H,x);lo=energy(*ref(d,q,True),x);hi=energy(*ref(d,q,False),x)
     if not lo<=u<=hi:fail.append({'x':str(x),'U':str(u),'lower':str(lo),'upper':str(hi)})
    rows.append({'n':n,'d':d,'sample':sample,'q':q,'edges':sorted(E),'histogram':H,'failures':fail})
   print(n,d,sample,'done',flush=True)
(L/'potts-results.json').write_text(json.dumps(rows,indent=2));print('cases',len(rows),'failures',sum(bool(r['failures']) for r in rows))
