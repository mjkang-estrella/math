import random,itertools as it,json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1];rng=random.Random(9402)
def F(a):
 w=[]
 for x in a:
  low=not w or w[-1]<=x;v=[];pending=[]
  for y in w:
   pending.append(y)
   if (y<=x)==low:v+=pending[-1:]+pending[:-1];pending=[]
  assert not pending
  w=v+[x]
 return w
def spots(a):
 used=set();r=[]
 for p in a:
  q=p
  while q in used:q+=1
  used.add(q);r.append(q)
 return r
def one(perm,bits):
 used=set();a=[]
 for j,s in enumerate(perm):
  p=s-1 if s-1 in used and bits>>j&1 else s
  a.append(p);used.add(s)
 assert spots(a)==list(perm)
 return a
out=[]
for n in range(2,41):
 count=0;fails=[]
 for rep in range(10000):
  p=list(range(1,n+1));rng.shuffle(p);a=one(p,rng.getrandbits(n));b=F(a);s=spots(b)
  if s!=F(p):fails.append([a,b,s,F(p)])
  count+=1
 r=dict(n=n,tested=count,failures=fails);print(r,flush=True);out.append(r)
 (D/'outputs/foata.json').write_text(json.dumps(out,indent=2)+'\n')
