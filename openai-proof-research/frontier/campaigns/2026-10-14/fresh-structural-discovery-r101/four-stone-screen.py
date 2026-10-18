"""Exact finite screen of Snaky completion threats from four owned stones."""
from itertools import combinations
from functools import lru_cache
import json
S=frozenset([(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)])
def orient(s,k):return frozenset(((-1 if k&1 else 1)*(y if k&4 else x),(-1 if k&2 else 1)*(x if k&4 else y)) for x,y in s)
def normalize(s):
 a=min(x for x,y in s);b=min(y for x,y in s)
 return tuple(sorted((x-a,y-b) for x,y in s))
def canon(s):return min(normalize(orient(s,k)) for k in range(8))
shapes={frozenset(normalize(orient(S,k))) for k in range(8)}
def targets(A,minimum):
 ts=set()
 for sh in shapes:
  for a in A:
   for x,y in sh:
    B=frozenset((u+a[0]-x,v+a[1]-y) for u,v in sh)
    if len(A&B)>=minimum:ts.add(B)
 return ts
@lru_cache(None)
def hit(es):
 if not es:return 0
 return 1+min(hit(tuple(e for e in es if x not in e)) for x in min(es,key=len))
triples={canon(a) for a in combinations(S,3)};fours=set()
for a in triples:
 A=frozenset(a)
 for t in targets(A,2):
  for z in t-A:fours.add(canon(A|{z}))
records=[]
for a in sorted(fours):
 A=frozenset(a);ts=targets(A,3);es=tuple(sorted(tuple(sorted(t-A)) for t in ts));v=hit(es)
 records.append({'initial':a,'targets':len(ts),'transversal':v})
maximum=max(r['transversal'] for r in records)
print(json.dumps({'status':'Four-stone completion screen; no full-game bound','types':len(records),'maximum_transversal':maximum,'maximizers':[r for r in records if r['transversal']==maximum]},indent=2))
