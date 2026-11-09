from generate_cases import *
from itertools import combinations
for a,b,e in [(7,4,0),(8,3,0),(8,4,0)]:
 cells=sorted([(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=a and e<=x-y<=e+b]);centers=[(x,y) for x in range(-10,12) for y in range(-10,12) if a-5<=x+y<=5 and e+b-5<=x-y<=e+5];holes={(2,2),(2,-2),(-2,2),(-2,-2)}
 groups={frozenset(p for p in cells if (p[0]-cx,p[1]-cy) in holes) for cx,cy in centers};groups.update(frozenset(p for p in cells if f(*p)==bd) for f,bd in [(lambda x,y:x+y,0),(lambda x,y:x+y,a),(lambda x,y:x-y,e),(lambda x,y:x-y,e+b)])
 forced=set.union(set(),*(set(g) for g in groups if len(g)==1));free=set(cells)-forced
 print((a,b,e),'forced',sorted(forced),'free',len(free))
 for add in combinations(sorted(free),11-len(forced)):
  P=forced|set(add);seen={min(P)}
  for _ in range(11):seen|={q for q in P if any(abs(q[0]-p[0])+abs(q[1]-p[1])==1 for p in seen)}
  if seen==P:print('connected',add,'miss',[sorted(g) for g in groups if not g&P])
