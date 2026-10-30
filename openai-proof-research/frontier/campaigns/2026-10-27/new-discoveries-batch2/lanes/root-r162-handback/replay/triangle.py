"""Exact local-state solver for cubic efficient-code triangle expansions."""
from pathlib import Path
import json,itertools,random
L=Path(__file__).resolve().parent
def solve(triples):
 k=len(triples);assert sorted(sum((list(t) for t in triples),[]))==sorted(list(range(k))*3)
 # Each triangle state: choose its cross-spoke subset A, then 0 or 1 internal edge.
 # Remember matched centers, centers adjacent to unmatched triangle leaves, size.
 states={(0,0):0}
 for t in triples:
  opts=[]
  for r in range(4):
   for aa in itertools.combinations(range(3),r):
    A=set(aa);rest=set(range(3))-A
    for internal in [None]+list(itertools.combinations(sorted(rest),2)):
     covered=A|set(internal or ());uncovered=set(range(3))-covered
     if len(uncovered)>1:continue # triangle leaves must be independent
     m=sum(1<<t[z] for z in A);req=sum(1<<t[z] for z in uncovered)
     opts.append((m,req,r+int(internal is not None)))
  new={}
  for (old,need),cost in states.items():
   for m,req,w in opts:
    if old&m:continue
    key=(old|m,need|req);new[key]=min(new.get(key,999),cost+w)
  states=new
 best=min(cost for (m,req),cost in states.items() if not req&~m)
 return best,len(states)
out=[]
families=[('fano',[(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)])]
rng=random.Random(20261030)
for k in range(3,9):
 for j in range(5):
  while True:
   a=list(range(k))*3;rng.shuffle(a);ts=[tuple(a[3*z:3*z+3]) for z in range(k)]
   if all(len(set(t))==3 for t in ts):break
  families.append((f'random-{k}-{j}',ts))
for name,ts in families:
 s,states=solve(ts);k=len(ts);out.append(dict(name=name,k=k,triples=ts,s=s,bound=(3*k+1)//2,terminal_states=states));print(name,s,(3*k+1)//2,flush=True)
(L/'triangle-checks.json').write_text(json.dumps(out,indent=2)+'\n')
