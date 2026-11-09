from itertools import combinations,permutations
from pathlib import Path
import json
# Direct backtracking with cut certificates on tiny hypergraphs.
out=[]
for N in range(3,6):
 tau=3;allE=list(combinations(range(N),tau));passed=0;tested=0;bad=[]
 for mask in range(1<<len(allE)):
  E=[e for j,e in enumerate(allE) if mask>>j&1]
  cuts=[S for S in range(1,(1<<N)-1)]
  crossing=[[j for j,e in enumerate(E) if any(S>>v&1 for v in e) and any(not(S>>v&1) for v in e)] for S in cuts]
  if any(len(c)<tau for c in crossing):continue
  passed+=1
  # break orientation permutation symmetry at first edge
  incoming=[[0]*tau for S in cuts];options=list(permutations(range(tau)))
  def dfs(j):
   if j==len(E):return all(all(a) for a in incoming)
   e=E[j]
   for p in (options[:1] if j==0 else options):
    changes=[]
    for ci,S in enumerate(cuts):
     if j in crossing[ci]:
      for o in range(tau):
       if S>>e[p[o]]&1:incoming[ci][o]+=1;changes.append((ci,o))
    viable=all(all(incoming[ci][o] or any(t>j for t in crossing[ci]) for o in range(tau)) for ci in range(len(cuts)))
    if viable and dfs(j+1):return True
    for ci,o in changes:incoming[ci][o]-=1
   return False
  ok=dfs(0);tested+=1
  if not ok:bad.append(E)
 r={'N':N,'tau':tau,'simple_hypergraphs_exhausted':1<<len(allE),'cut_connected_cases':passed,'orientation_cases_tested':tested,'failures':bad};out.append(r);print(r,flush=True)
Path('outputs/orient.json').write_text(json.dumps(out,indent=2)+'\n')
