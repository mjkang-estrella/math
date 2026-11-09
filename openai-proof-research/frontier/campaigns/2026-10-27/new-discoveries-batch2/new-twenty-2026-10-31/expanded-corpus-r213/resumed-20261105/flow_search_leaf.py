from functools import lru_cache
from collections import defaultdict
import json,sys
N=int(sys.argv[1]); trees={1:[()]}
@lru_cache(None)
def size(t):return 1+sum(map(size,t))
def add(a,b):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+v
 return {k:v for k,v in c.items() if v}
def mulq(a,b):
 c=defaultdict(int)
 for (i,j),v in a.items():
  for (k,l),w in b.items():c[i+k,j+l+1]+=v*w
 return dict(c)
def splits(t):
 # Each occurrence of v non-root and each of its children w; canonical rooted tuples.
 for i,v in enumerate(t):
  for j,w in enumerate(v):
   if w:continue
   vv=v[:j]+v[j+1:]; moved=tuple(sorted(t[:i]+t[i+1:]+(vv,w)))
   bottom=tuple(sorted(t[:i]+t[i+1:]+((),)))
   yield moved,bottom,v
  for moved,bottom,top in splits(v):
   yield tuple(sorted(t[:i]+t[i+1:]+(moved,))),tuple(sorted(t[:i]+t[i+1:]+(bottom,))),top
@lru_cache(None)
def f(t):
 if not t:return {(0,-1):1}
 if t==((),):return {(0,-2):1,(1,-1):1}
 if all(not x for x in t):
  from math import comb
  n=len(t);return {(1,j-(n-1)):(-1)**(n-2-j)*comb(n-2,j) for j in range(n-1)}
 a,b,c=next(splits(t));return add(f(a),mulq(f(b),f(c)))
for n in range(2,N+1):
 pool=sorted(t for k in range(1,n) for t in trees[k]); out=[]
 def gen(rem,start,parts):
  if rem==0:out.append(tuple(parts));return
  for i in range(start,len(pool)):
   z=pool[i];s=size(z)
   if s<=rem:gen(rem-s,i,parts+[z])
 gen(n-1,0,[]);trees[n]=sorted(out)
 checked=0;bad=[]
 for t in trees[n]:
  target=f(t)
  for a,b,c in splits(t):
   checked+=1
   if target!=add(f(a),mulq(f(b),f(c))):bad.append(repr(t))
 print(json.dumps({'n':n,'rooted_unlabelled_trees':len(out),'all_graft_relations_checked':checked,'failures':bad[:2],'f_cache':f.cache_info().currsize}),flush=True)
 if bad:break
