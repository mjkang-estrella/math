"""Bounded independent generator-factorization check; not a proof or mathematical gate."""
from functools import lru_cache
from math import comb
from pathlib import Path
import json
root=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r127')
rows=[]
for r in (2,3,4,5,7,8):
 gens=[(1,1,0),(0,1,1),(0,r,0)]+[(r-i,0,i) for i in range(r+1)]
 @lru_cache(None)
 def order(a,b,c):
  if a==b==c==0:return 0
  vals=[1+order(a-u,b-v,c-w) for u,v,w in gens if a>=u and b>=v and c>=w]
  return max(vals,default=-100000)
 for q in range(1,6):
  count=0
  for a in range(r*q):
   for b in range(r*q):
    for c in range(r*q):
     if (a-b+c)%r==0 and order(a,b,c)<q:count+=1
  formula=(r+2)*comb(q+1,3)+comb(q+1,2)
  rows.append(dict(r=r,q=q,count_by_generator_recursion=count,formula=formula,agree=count==formula))
 assert all(x['agree'] for x in rows)
(root/'private/quotient-diagnostic.json').write_text(json.dumps({'scope':'six r values and q=1,...,5; enumeration cannot prove all r,q; no gates','rows':rows},indent=2)+'\n')
print('30 finite Hilbert-function comparisons agree; no mathematical verdict.')
