from itertools import permutations,combinations
from functools import lru_cache
from pathlib import Path
import json,sys,random
D=Path(__file__).resolve().parents[1]
def std(v):return tuple(sorted(v).index(a) for a in v)
def run(k,n,trials=0):
 pats=list(permutations(range(k)));idx={p:i for i,p in enumerate(pats)};rev=[idx[p[::-1]] for p in pats];seen=set()
 for pi in permutations(range(n)):
  seen.add(sum(1<<i for i in {idx[std(tuple(pi[j] for j in c))] for c in combinations(range(n),k)}))
 masks=sorted(seen);contain=[sum(1<<j for j,m in enumerate(masks) if m>>i&1) for i in range(len(pats))];start=(1<<len(masks))-1;failures=[];states=0
 def failure(s):
  for p in range(len(pats)):
   if s&contain[p] and not (s&~contain[p])&contain[rev[p]]:return p
 if trials:
  rng=random.Random(90)
  for _ in range(trials):
   s=start
   while s:
    states+=1;p=failure(s)
    if p is not None:
     if len(failures)<10:failures.append({'remaining_pattern_sets':s.bit_count(),'first_pattern':pats[p]})
     break
    moves=[i for i in range(len(pats)) if s&contain[i]]
    p=rng.choice(moves);s=s&~contain[p]&~contain[rev[p]]
 else:
  @lru_cache(None)
  def dfs(s):
   nonlocal states
   states+=1;p=failure(s)
   if p is not None:
    if len(failures)<10:failures.append({'remaining_pattern_sets':s.bit_count(),'first_pattern':pats[p]})
    return False
   ok=True
   for p in range(len(pats)):
    if s&contain[p]:ok=dfs(s&~contain[p]&~contain[rev[p]]) and ok
   return ok
  dfs(start)
 r={'k':k,'n':n,'permutations_exhausted':__import__('math').factorial(n),'distinct_pattern_sets':len(masks),'reverse_states_tested':states,'random_trials':trials,'failure_examples':failures,'scope':'all reachable reverse states' if not trials else 'random reverse trajectories; exhaustive occurrence generation'}
 (D/f'outputs/game-{k}-{n}.json').write_text(json.dumps(r,indent=2)+'\n');print(r,flush=True)
for k,n in [(3,3),(3,4),(3,5),(3,6),(4,4),(4,5),(4,6),(4,7),(4,8),(5,5),(5,6),(5,7)]:run(k,n,1000 if k==5 else 0)
