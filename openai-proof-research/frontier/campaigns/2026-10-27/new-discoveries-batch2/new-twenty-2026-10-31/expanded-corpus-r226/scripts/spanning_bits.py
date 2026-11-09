from pathlib import Path
from itertools import combinations_with_replacement
from math import gcd
import sys,json
L=Path(__file__).resolve().parents[1];lo,hi=map(int,sys.argv[1:]);out=[]
for k in range(lo,hi+1):
 n=2*k;mask=(1<<n)-1;full=(1<<(2*n))-1;best=n;witness=None;count=0
 # Replace each generator by its inverse: y in [0,k]. Pairs differing only by signs have the same metric.
 gens=[(x,y) for x in range(2) for y in range(k+1)]
 for a,b in combinations_with_replacement(gens,2):
  if a==b:continue
  count+=1
  if gcd(gcd(a[1],b[1]),n)>1 or (a[0]==0 and b[0]==0):continue
  if (a[0]*b[1]-b[0]*a[1])%2==0:continue
  steps=tuple(set((x,z%n) for x,y in (a,b) for z in (y,-y)))
  bits=1;radius=0
  while radius<best:
   v=bits
   for x,y in steps:
    aa=bits&mask;bb=bits>>n
    if y:aa=((aa<<y)|(aa>>(n-y)))&mask;bb=((bb<<y)|(bb>>(n-y)))&mask
    if x:aa,bb=bb,aa
    v|=aa|(bb<<n)
   radius+=1
   if v==full:best=radius;witness=[a,b];break
   if v==bits:break
   bits=v
 predicted=next(s for s in range(1,n+1) if (s%2 and 2*k<=s*s-1) or (not s%2 and (2*k<=s*s-s or (2*k<=s*s and ((s%4==0 and k%2==0) or (s%4==2 and k%4==2))))))
 row=dict(k=k,sign_representative_pairs=count,min_radius=best,predicted=predicted,witness=witness);print(json.dumps(row),flush=True);out.append(row)
 if best!=predicted:print('MISMATCH',flush=True);break
(L/f'inputs/spanning-bits-{lo}-{hi}.json').write_text(json.dumps(out,indent=2)+'\n')
