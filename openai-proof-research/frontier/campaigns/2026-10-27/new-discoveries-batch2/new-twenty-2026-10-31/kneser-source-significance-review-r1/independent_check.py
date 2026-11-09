from itertools import combinations
from collections import Counter
from pathlib import Path
import json,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
# Independently generate integer bitmask pairs; choose missing four, not author's family search.
pairs=[(1<<i)|(1<<j) for i,j in combinations(range(6),2)]
hist=Counter(); edgehist=Counter(); worst=[];min_edges=100
for missing in combinations(pairs,4):
 fam=[x for x in pairs if x not in missing]
 deg=[sum(x&y==0 for y in fam) for x in fam];hist[max(deg)]+=1;edgehist[sum(deg)//2]+=1
 if sum(deg)//2<min_edges:min_edges=sum(deg)//2;worst=fam
b=[(1<<i)|(1<<j) for i,j in combinations(range(7),2) if i>=5 or j>=5]
out={'compressed_count':sum(hist.values()),'max_degree_histogram':dict(hist),'induced_edge_histogram':dict(edgehist),'minimum_induced_edges':min_edges,'min_edge_example_masks':worst,'witness_masks':b,'witness_degrees':[sum(x&y==0 for y in b) for x in b]}
Path(__file__).with_name('independent-check.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
