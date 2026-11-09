from pathlib import Path
from functools import lru_cache
import sys,json
L=Path(__file__).resolve().parents[1];n=int(sys.argv[1]);calls=0
adj=[[] for _ in range(2*n)]
for u in range(n):
 for v in range(n):
  e=1<<(u*n+v);adj[u].append((n+v,e));adj[n+v].append((u,e))
@lru_cache(None)
def win(mask,cur,opp):
 global calls
 calls+=1
 if calls%500000==0:print('states',calls,flush=True)
 for v,e in adj[cur]:
  if mask&e and not win(mask^e,opp,v):return True
 return False
# First move fixed 0 -> n by graph symmetries. Second player's initial oriented edge is unrestricted except used edge.
mask=((1<<(n*n))-1)^1;answers=[]
for u in range(2*n):
 for v,e in adj[u]:
  if mask&e:
   w=not win(mask^e,n,v);answers.append([u,v,w])
   print('initial',u,v,'P2win',w,'states',calls,flush=True)
print(json.dumps(dict(n=n,p2win=any(x[2] for x in answers),initial_moves=len(answers),states=calls,cache=str(win.cache_info()))),flush=True)
(L/f'inputs/trail-{n}.json').write_text(json.dumps(dict(n=n,p2win=any(x[2] for x in answers),initial_answers=answers,states=calls),indent=2)+'\n')
