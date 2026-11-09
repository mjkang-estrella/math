from itertools import product,combinations
import json

def image(out,S):
 a=0
 for i in range(len(out)):
  if S>>i&1:a|=out[i]
 return a

def search(n):
 pairs=list(combinations(range(n),2)); total=weak=strict=0; example=None
 for cfg in product(range(3),repeat=len(pairs)):
  out=[0]*n
  for (u,v),c in zip(pairs,cfg):
   if c==1:out[u]|=1<<v
   elif c==2:out[v]|=1<<u
  full=(1<<n)-1
  if not all(out):continue
  good=True
  for i in range(n):
   S=1<<i
   for _ in range(n):S|=image(out,S)
   if S!=full:good=False;break
  if not good:continue
  total+=1
  F=[image(out,S) for S in range(1<<n)]
  ds=[(F[F[S]]&~F[S]).bit_count()-(F[S]&~S).bit_count() for S in range(1,full)]
  if max(ds)>0:continue
  weak+=1
  if any((F[F[1<<i]]&~F[1<<i]).bit_count()<F[1<<i].bit_count() for i in range(n)):
   strict+=1
   if example is None:example={'out':out,'deficits':ds}
 return {'n':n,'strong':total,'weak':weak,'strict_singleton':strict,'example':example}
print(json.dumps([search(n) for n in range(3,6)],indent=2))
