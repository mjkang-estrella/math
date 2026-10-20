#!/usr/bin/env python3
"""MIT. Finite diagnostics of the reassessment reduction, not a correctness gate."""
from itertools import permutations,combinations
import json

def cross(a,b):return a[0]*b[1]-a[1]*b[0]
pts=[(1,0),(0,1),(-1,0),(0,-1)]
integer_cases=0
for perm in permutations(range(4)):
 pos={v:i for i,v in enumerate(perm)}
 val=sum(e*f*(pos[u]<pos[w]) for u,e in [(0,-1),(1,1)] for w,f in [(2,-1),(3,1)])
 a,b,c,d=[pts[pos[i]] for i in range(4)]
 alt=((pos[0]<pos[2]<pos[1]) != (pos[0]<pos[3]<pos[1])) if pos[0]<pos[1] else ((pos[1]<pos[2]<pos[0]) != (pos[1]<pos[3]<pos[0]))
 det=cross((b[0]-a[0],b[1]-a[1]),(d[0]-c[0],d[1]-c[1]))
 actual=(1 if det>0 else -1) if alt else 0
 assert val==actual,(perm,val,actual)
 integer_cases+=1
shared_cases=0
for n in range(2,8):
 for offset in [-0.1,0.1]:
  delta=int(offset>0)
  for z in combinations(range(n),2):
   for y in combinations(range(n),2):
    a,b=z;c,d=[v+offset for v in y]
    alternate=int((a<c<b)!=(a<d<b))
    expanded=sum(int(e<f) if e!=f else delta for e in z for f in y)%2
    assert alternate==expanded
    shared_cases+=1
order_cases=0
for n in range(3,18,2):
 s=(n-1)//2
 for p in range(n):
  for q in range(n):
   up=int(p<q);lo=int(q<p)
   assert up^lo == int(p!=q)
   if p!=q:
    source=lo^int(p>s)
    author=up^int(p<=s)
    target=int((q<p<=s) or (s<p<q))
    assert source==author==target
   order_cases+=1
print(json.dumps({'integer_chord_orders':integer_cases,'shared_spoke_local_cases':shared_cases,'order_support_entries':order_cases,'all_pass':True,'limit':'finite diagnostics; no all-drawing or correctness certification'},sort_keys=True))
