from itertools import combinations
from random import Random
from fractions import Fraction
import json

def rank(n,edges,mask):
 p=list(range(n))
 def f(a):
  while p[a]!=a:a=p[a]
  return a
 r=0
 for i,(u,v) in enumerate(edges):
  if mask>>i&1:
   a,b=f(u),f(v)
   if a!=b:p[a]=b;r+=1
 return r
rng=Random(137); records=[]
for n in range(4,9):
 best=None
 for trial in range(120):
  edges=[]
  for color in range(2):
   order=list(range(n));rng.shuffle(order)
   edges += [(order[i],order[rng.randrange(i)]) for i in range(1,n)]
  m=len(edges);full=(1<<m)-1;b=n-1
  subsets=[sum(1<<i for i in z) for z in combinations(range(m),b)]
  rr={a:rank(n,edges,a) for a in subsets}
  good=[a for a in subsets if rr[a]==b and rr[full^a]==b]
  for a in rng.sample(subsets,min(120,len(subsets))):
   d1,d2=b-rr[a],b-rr[full^a]
   if d1+d2!=1:continue
   dist=min((a^g).bit_count()//2 for g in good)
   if best is None or dist>best['swaps']:
    best={'n':n,'edges':edges,'A':[i for i in range(m) if a>>i&1],'d1':d1,'d2':d2,'swaps':dist,'nearest':[i for i in range(m) if min(good,key=lambda g:(a^g).bit_count())>>i&1]}
  if best and best['swaps']>=3:break
 records.append(best)
 print(json.dumps(best),flush=True)
open('work/repair-exploration.json','w').write(json.dumps(records,indent=2)+'\n')
