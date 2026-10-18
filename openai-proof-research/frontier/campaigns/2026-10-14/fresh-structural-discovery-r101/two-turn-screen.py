"""Exact finite two-turn screen; not a bound for games with more turns."""
from itertools import combinations
from functools import lru_cache
import json
S=frozenset([(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)])
def orient(s,k):
 return frozenset(((-1 if k&1 else 1)*(y if k&4 else x),(-1 if k&2 else 1)*(x if k&4 else y)) for x,y in s)
def normalize(s):
 a=min(x for x,y in s);b=min(y for x,y in s)
 return tuple(sorted((x-a,y-b) for x,y in s))
def canon(s):return min(normalize(orient(s,k)) for k in range(8))
shapes={frozenset(normalize(orient(S,k))) for k in range(8)}
triples={canon(a) for a in combinations(S,3)}
@lru_cache(None)
def transversal(es):
 if not es:return 0
 edge=min(es,key=len)
 return 1+min(transversal(tuple(e for e in es if x not in e)) for x in edge)
records=[]
for a in sorted(triples):
 A=set(a);targets=set()
 for sh in shapes:
  for x,y in sh:
   ax,ay=a[0];B=frozenset((u+ax-x,v+ay-y) for u,v in sh)
   if A<=B:targets.add(B)
 edges=tuple(sorted(tuple(sorted(B-A)) for B in targets))
 records.append({'initial':a,'targets':len(targets),'transversal':transversal(edges)})
print(json.dumps({'status':'finite two-turn screen only','initial_D4_translation_types':len(records),'maximum_transversal':max(r['transversal'] for r in records),'records':records},indent=2))
