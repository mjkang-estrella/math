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
