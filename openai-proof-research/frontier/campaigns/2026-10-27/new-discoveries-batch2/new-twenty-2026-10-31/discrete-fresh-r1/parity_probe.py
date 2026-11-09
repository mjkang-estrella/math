"""Exploratory Gauss-code model. Specialization s=3,t=2. Not a knot certificate.
The source's full diagram/invariance bridges are NOT formalized.
"""
from fractions import Fraction as F
from pathlib import Path
import random,json
P=Path(__file__).resolve().parent

def probe(word,overs,signs):
 n=len(signs);pos=[[i for i,x in enumerate(word) if x==j] for j in range(n)]
 odd=[(b-a-1)%2 for a,b in pos]
 over=[pos[j][overs[j]] for j in range(n)];under=[pos[j][1-overs[j]] for j in range(n)]
 active=sorted(under[j] for j in range(n) if not odd[j]);m=len(active)
 if not m:return None
 factors={}
 for j in range(n):
  if odd[j]:
   factors[over[j]]=(F(1),signs[j]);factors[under[j]]=(F(1),-signs[j])
  else:factors[over[j]]=(F(3)**signs[j],0)
 def transport(i):
  coef=F(1);exp=0
  while i not in active:
   a,b=factors[i];coef*=a;exp+=b;i=(i-1)%(2*n)
  return active.index(i),coef,exp
 rows=[]
 for row,i in enumerate(active):
  j=word[i];sg=signs[j];terms=[(row,F(1),0)]
  a,b,c=transport((i-1)%(2*n));terms.append((a,-F(2)**sg*b,c))
  a,b,c=transport((over[j]-1)%(2*n));terms.append((a,-(1-F(6)**sg)*b,c))
  rows.append(terms)
 dp={0:{0:F(1)}}
 for row,terms in enumerate(rows):
  new={}
  for mask,poly in dp.items():
   for col,coef,exp in terms:
    if mask>>col&1:continue
    sign=(-1)**((mask>>(col+1)).bit_count());dest=new.setdefault(mask|(1<<col),{})
    for e,c in poly.items():dest[e+exp]=dest.get(e+exp,F(0))+c*coef*sign
  dp=new
 poly={e:c for e,c in dp[(1<<m)-1].items() if c}
 return dict(odd_crossings=sum(odd),even_crossings=m,polynomial={str(e):str(c) for e,c in poly.items()},span=max(poly)-min(poly) if poly else None)
example=probe([0,1,0,2,1,2],[0,0,0],[-1,-1,1])
# Expected source Example 2.1 after specialization: (5/6)*(1-z^-2), up to unit.
assert example['polynomial']=={'0':'5/6','-2':'-5/6'},example
rng=random.Random(321278);report={'caveat':__doc__,'source_example_2_1':example,'runs':[]}
for n in [6,7,8,9,10,12]:
 tested=0;viol=[];maxspan=0
 for _ in range(200):
  w=list(range(n))*2;rng.shuffle(w);ov=[rng.randrange(2) for j in range(n)];sg=[rng.choice([-1,1]) for j in range(n)]
  r=probe(w,ov,sg);tested+=1
  if r and r['span'] is not None:
   maxspan=max(maxspan,r['span'])
   if r['span']>n:viol.append(dict(word=w,overs=ov,signs=sg,result=r))
 report['runs'].append(dict(n=n,tested=tested,max_specialized_span=maxspan,violations=viol))
(P/'parity-diagnostics.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
