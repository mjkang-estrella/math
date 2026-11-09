from itertools import combinations
from pathlib import Path
import json
out=[]
for n,k,H in [(5,3,4),(6,3,4),(6,4,3)]:
 calls=list(combinations(range(n),k));start=tuple(1<<i for i in range(n));states={start};greedy={start};rows=[]
 def step(s,c):
  u=0
  for i in c:u|=s[i]
  t=list(s)
  for i in c:t[i]=u
  return tuple(t)
 def score(s):return sum(x.bit_count() for x in s)
 for h in range(1,H+1):
  ns=set();ng=set();stopped=False
  for s in states:
   for c in calls:
    ns.add(step(s,c))
    if len(ns)>80000:stopped=True;break
   if stopped:break
  if stopped:rows.append(dict(calls=h,stopped='80000-state cap; no complete layer claim'));break
  for s in greedy:
   nxt=[step(s,c) for c in calls];best=max(map(score,nxt));ng.update(t for t in nxt if score(t)==best)
  states=ns;greedy=ng;opt=max(map(score,states));gmin=min(map(score,greedy));gmax=max(map(score,greedy))
  rows.append(dict(calls=h,states=len(states),greedy_states=len(greedy),optimal=opt,greedy_min=gmin,greedy_max=gmax,full_gossip_possible=opt==n*n))
  if opt==n*n:break
 out.append(dict(n=n,k=k,layers=rows))
p=Path(__file__).resolve().parent/'calculation.json';p.write_text(json.dumps(out,indent=2)+'\n');print(p.read_text())
