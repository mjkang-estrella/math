from functools import lru_cache
from collections import defaultdict
from math import factorial
import sys,json,time
n=int(sys.argv[1]);twist=int(sys.argv[2]);e=tuple(range(1,n+1));target=tuple(-i if i>1 or n%2==0 else i for i in e)
def right(y,s):
 z=list(y);i=0 if s==0 else s-1;z[i],z[i+1]=z[i+1],z[i]
 if s==0:z[0]=-z[0];z[1]=-z[1]
 return tuple(z)
def left(y,s):
 a,b=(1,2) if s==0 else (s,s+1)
 def f(v):
  k=abs(v);sgn=1 if v>0 else -1
  return sgn*(-1 if s==0 else 1)*(b if k==a else a) if k in (a,b) else v
 return tuple(map(f,y))
@lru_cache(None)
def length(y):return sum(a>b for i,a in enumerate(y) for b in y[i+1:])+sum(-a>b for i,a in enumerate(y) for b in y[i+1:])
@lru_cache(None)
def step(y,s):
 r=right(y,s);u=left(y,1-s if twist and s<2 else s)
 if length(r)<length(y):return None
 return r if u==r else left(r,1-s if twist and s<2 else s)
# All accepted collapsed words counted once by determinizing the finite involution weak-order automaton.
layer={frozenset([e]):1};depth=0;accepted=0;states=0;maxset=0
while layer:
 nxt=defaultdict(int);states+=len(layer);maxset=max(maxset,max(map(len,layer)))
 for ys,count in layer.items():
  if target in ys:accepted+=count;continue
  for label in range(1,n):
   gens=(0,1) if label==1 else (label,)
   zs=frozenset(z for y in ys for s in gens if (z:=step(y,s)) is not None)
   if zs:nxt[zs]+=count
 print(json.dumps({'n':n,'twist':twist,'depth':depth,'dfa_states':len(layer),'accepted':accepted,'cache':step.cache_info().currsize}),flush=True)
 layer=nxt;depth+=1
h=n//2 if not twist else (n+1)//2-1
shape=list(range(n-1,h-1,-1))+list(range(h,0,-1));total=sum(shape);den=1
for i,row in enumerate(shape):
 for j in range(row):den*=row-j+sum(r>j for r in shape[i+1:])
f=factorial(total)//den
print(json.dumps({'RESULT':True,'n':n,'twist':twist,'count':accepted,'shape':shape,'hook_count':f,'equal':accepted==f,'states':states,'max_subset':maxset}),flush=True)
