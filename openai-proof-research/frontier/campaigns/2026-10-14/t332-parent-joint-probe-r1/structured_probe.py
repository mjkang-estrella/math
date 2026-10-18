#!/usr/bin/env python3
"""MIT. A denser finite test around a boundary face; not a theorem."""
import itertools,json
from probe import flow,solve,unique
for name,parent,weights in [
 ('binary7_cube',[-1,0,0,1,1,2,2],[1]*7),
 ('binary7_cube_short_leaves',[-1,0,0,1,1,2,2],[1,1,1,.125,.125,.125,.125]),
 ('comb7_cube',[-1,0,0,1,1,3,3],[1]*7)]:
 d=len(parent);leaf=[all(p!=e for p in parent) for e in range(d)]
 base=flow(parent,[4 if leaf[e] else 0 for e in range(d)])
 anchors=[[0]*d,base];points=[]
 for bits in itertools.product((-1,1),repeat=d):
  x=[a+b for a,b in zip(base,bits)]
  feasible=all(x[e]>=sum(x[f] for f,p in enumerate(parent) if p==e) for e in range(d))
  (anchors if feasible else points).append(x)
 for e in range(d):
  for c in ([-2,2] if leaf[e] else [2]):
   delta=flow(parent,[c if j==e else 0 for j in range(d)])
   anchors.append([x+y for x,y in zip(base,delta)])
 anchors=unique(anchors);points=unique(points)
 case={'name':name,'parent':parent,'weights':weights,'anchors':anchors,'points':points}
 case['result']=solve(parent,weights,anchors,points)
 print(json.dumps(case),flush=True)
