from pathlib import Path
from collections import deque,Counter
import json,resource,os
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
v=[(i,a) for i in range(12) for a in range(4)]
n={x:{y for y in v if (y[0]-x[0])%12 in (1,11) and x[1]!=y[1]} for x in v}
def bfs(x,deleted=None):
 d={x:0};q=deque([x])
 while q:
  u=q.popleft()
  for y in n[u]:
   if y!=deleted and y not in d:d[y]=d[u]+1;q.append(y)
 return d
base={x:bfs(x) for x in v}
changes=[];pairs=0
for z in v:
 for x in v:
  if x==z:continue
  d=bfs(x,z)
  for y in v:
   if y!=z:
    pairs+=1
    if d.get(y)!=base[x].get(y):changes.append([z,x,y])
surround=[(x,y) for x in v for y in v if x!=y and n[x]<=(n[y]|{y})]
common=Counter(len(n[x]&n[y]) for x in v for y in v if x!=y and y not in n[x])
out={'vertices':len(v),'edges':sum(map(len,n.values()))//2,'degree_set':sorted(set(map(len,n.values()))),'connected':all(len(d)==48 for d in base.values()),'diameter':max(max(d.values()) for d in base.values()),'antipodal_distance':base[(0,0)][(6,0)],'all_ordered_surviving_pair_checks':pairs,'deletion_distance_changes':changes,'surrounding_ordered_pairs':surround,'common_neighbor_counts_nonadjacent_distinct':dict(common),'diagnostic_only':True}
Path(__file__).with_name('diagnostic.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
