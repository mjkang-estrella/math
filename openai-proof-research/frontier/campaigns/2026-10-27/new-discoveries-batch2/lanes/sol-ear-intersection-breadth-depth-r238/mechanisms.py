from pathlib import Path
from functools import lru_cache
from math import comb
import json,itertools
L=Path(__file__).resolve().parent
def cat(k):return comb(2*k,k)//(k+1)
@lru_cache(None)
def tri(v):
 if len(v)<3:return (frozenset(),)
 ans=[]
 for j in range(1,len(v)-1):
  for a in tri(v[:j+1]):
   for b in tri(v[j:]):
    es=set(a|b)
    for x,y in [(v[0],v[j]),(v[j],v[-1])]:
     if y-x>1:es.add((x,y))
    ans.append(frozenset(es))
 return tuple(ans)
def ears(t,n):return frozenset(i for i in range(n) if tuple(sorted(((i-1)%n,(i+1)%n))) in t)
def transfer(t):
 # Remove vertex 2 and its ear, relabel old vertex 1 as 2, insert new ear at 1.
 assert (1,3) in t
 def f(x):return 2 if x==1 else x
 return frozenset({tuple(sorted((f(a),f(b)))) for a,b in t if (a,b)!=(1,3)}|{(0,2)})
out={'literal_transfer':[],'boundary_falsification':[],'deficit_test':[],'hall_repair':[]}
for n in range(5,10):
 ts=[t-{(0,n-1)} for t in tri(tuple(range(n)))];es={t:ears(t,n) for t in ts};universe=set(ts)
 maps={t:transfer(t) for t in ts if 2 in es[t]};assert len(set(maps.values()))==cat(n-3)
 assert all(u in universe and 1 in es[u] for u in maps.values())
 # Test size-preserving transfer on full literal-ear stars, not a set-weight shift.
 for j in range(n):
  F={t for t in ts if j in es[t]};G={maps[t] if t in maps and maps[t] not in F else t for t in F}
  assert len(G)==len(F)
  bad=next(((a,b) for a,b in itertools.combinations(G,2) if not es[a]&es[b]),None)
  if bad:
   out['literal_transfer'].append(dict(n=n,original_star=j,size=len(F),pair=[sorted(t) for t in bad],pair_ears=[sorted(es[t]) for t in bad]));break
 w={}
 F={t for t in ts if 0 in es[t]};kept={t for t in F if 2 not in es[t]};moved=F-kept
 candidates={t for t in ts if 1 in es[t] and all(es[t]&es[u] for u in kept)}
 out['hall_repair'].append(dict(n=n,kept=len(kept),demand=len(moved),all_compatible_ear1_targets=len(candidates),targets=[sorted(t) for t in candidates] if n<=6 else None))
 for t,s in es.items():w[s]=w.get(s,0)+1
 # Strong boundary induction hypothesis: after forbidding any ears B, the
 # remaining exact-ear measure is EKR with bound its largest conditional star.
 # Test the noncontiguous three-site boundary pattern first.
 B=frozenset({1,3,5}) if n>=6 else frozenset()
 vs=[s for s in w if not s&B];bound=max((sum(w[s] for s in vs if i in s) for i in range(n)),default=0)
 for A in itertools.combinations(vs,3):
  if all(a&b for a,b in itertools.combinations(A,2)) and sum(w[s] for s in A)>bound:
   out['boundary_falsification'].append(dict(n=n,forbidden=sorted(B),family=[sorted(s) for s in A],weights=[w[s] for s in A],conditional_star_bound=bound));break
 # A natural symmetric deficit inequality for the C/D split:
 # |F\F02|+|F13| <= C_(n-3). It must hold for every rotated star if universal.
 for j in range(n):
  F=[s for s in w if j in s];a=sum(w[s] for s in F if {0,2}<=s);b=sum(w[s] for s in F if {1,3}<=s)
  if b>a:out['deficit_test'].append(dict(n=n,star=j,F02=a,F13=b,total=cat(n-3),claimed_left=cat(n-3)-a+b));break
(L/'mechanisms.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
