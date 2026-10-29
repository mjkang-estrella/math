from check import feasible,points,P
from collections import defaultdict,Counter
import json
pts=points(3,3);ss=set(pts);fs=defaultdict(set)
for a in pts:
 for b in pts:fs[tuple(x+y for x,y in zip(a,b))].add(a)
rounding=None;degree=None
for w,F in fs.items():
 s=sum(w)
 if s%2:continue
 k=s//2
 lo=tuple(z//2 for z in w);odds=[i for i,z in enumerate(w) if z%2];c=list(lo)
 for i in odds[:len(odds)//2]:c[i]+=1
 c=tuple(c);d=tuple(z-x for z,x in zip(w,c))
 if rounding is None and (c not in ss or d not in ss):rounding=dict(w=w,round=c,complement=d,balanced_valid=next((x for x in F if sum(x)==k),None))
 left=[x for x in F if sum(x)==k-1];right=[x for x in F if sum(x)==k]
 if not left or not right:continue
 def neighbor(x,j,step):return tuple(z+(step if i==j else 0) for i,z in enumerate(x))
 od=[sum(neighbor(x,j,1) in F for j in range(5)) for x in left]
 ind=[sum(neighbor(x,j,-1) in F for j in range(5)) for x in right]
 if degree is None and min(od)<max(ind):degree=dict(w=w,k=k,left_count=len(left),right_count=len(right),left_degrees=Counter(od),right_degrees=Counter(ind))
print(json.dumps(dict(rounding_obstruction=rounding,crude_degree_obstruction=degree),indent=2))
(P/'fiber.json').write_text(json.dumps(dict(rounding_obstruction=rounding,crude_degree_obstruction=degree),indent=2)+'\n')
