from itertools import product,combinations
from fractions import Fraction
import json,random
rng=random.Random(23968)
report=[]
for n in [4,5,6]:
 signs=list(product([-1,1],repeat=n)); weights=[x.count(1) for x in signs]
 rows=[a for a in product([-1,0,1],repeat=n) if any(a) and next(x for x in a if x)!=-1]
 masks=[]
 for a in rows:
  masks.append(sum(1<<i for i,x in enumerate(signs) if sum(ai*xi for ai,xi in zip(a,x))==0))
 maxima={p:(Fraction(-1),None) for p in [Fraction(1,10),Fraction(1,4),Fraction(2,5),Fraction(1,2)]}; count=0
 histset=set()
 for i,j in combinations(range(len(rows)),2):
  a,b=rows[i],rows[j]
  if not any(a[r]*b[s]!=a[s]*b[r] for r in range(n) for s in range(r)):continue
  mask=masks[i]&masks[j];h=[0]*(n+1)
  while mask:
   bit=mask&-mask;h[weights[bit.bit_length()-1]]+=1;mask-=bit
  h=tuple(h);count+=1
  if h in histset:continue
  histset.add(h)
  for p in maxima:
   mass=sum(Fraction(c)*p**k*(1-p)**(n-k) for k,c in enumerate(h))
   assert mass<=p**3+(1-p)**3,(n,a,b,p,mass)
   if mass>maxima[p][0]:maxima[p]=(mass,[a,b,h])
 report.append({'n':n,'integer_constraint_pairs':count,'distinct_intersection_weight_histograms':len(histset),'maxima':{str(p):{'mass':str(v[0]),'equal_to_proposed_bound':v[0]==p**3+(1-p)**3,'example':v[1]} for p,v in maxima.items()}})
print(json.dumps({'scope':'codimension2; coefficient rows in{-1,0,1}; n4,5,6; four rational biases only; not all real subspaces and not proof','results':report},indent=2))
