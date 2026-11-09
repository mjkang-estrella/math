import itertools,json
from pathlib import Path
rows=[]
for n in range(7,13):
 r=5; found=0; examined=0
 for b in itertools.combinations(range(n),r):
  examined+=1;B=[{(a+t)%n for a in b} for t in range(n)]
  if min(len(B[0]&B[t]) for t in range(1,n))>=2:
   found+=1
   if n==9 and found==1: chosen=b
 rows.append({'n_per_side':n,'r':r,'all_cyclic_blocks_tested':examined,'pairwise_intersections_at_least_two':found})
n=9;B=[{(a+t)%n for a in chosen} for t in range(n)]
E={(a,b) for a in range(18) for b in range(a+1,18) if b<9 or a<9 and b-9 in B[a]}
adj=[{b if a==v else a for a,b in E if v in (a,b)} for v in range(18)]
checks=0;bad=[]
for c in range(18):
 for L in itertools.combinations(sorted(adj[c]),6):
  checks+=1;edges=sum(tuple(sorted((a,b))) in E for a,b in itertools.combinations(L,2))
  if edges<=1:bad.append((c,L,edges))
conn=0
for k in range(5):
 for rem in itertools.combinations(range(18),k):
  left=set(range(18))-set(rem);seen={min(left)};stack=list(seen)
  while stack:
   for v in adj[stack.pop()]&left-seen:seen.add(v);stack.append(v)
  assert seen==left;conn+=1
assert not bad
out={'cyclic_sweep':rows,'chosen_offsets':chosen,'edges':sorted(E),'degrees':[len(a) for a in adj],'neighbour_sets':B,'forbidden_center_leafsets_tested':checks,'forbidden_found':bad,'deletion_sets_tested':conn,'hamilton_obstruction':'Both endpoints in the clique require at least ten clique vertices to separate the nine independent vertices. Only nine exist.'}
out['neighbour_sets']=[sorted(x) for x in B]
Path('outputs/split-search.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
