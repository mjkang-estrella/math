from pathlib import Path
from collections import defaultdict
import json
L=Path(__file__).resolve().parent
sig=defaultdict(lambda:[0]*17);levels=[0]*29;p=[0]*29;p[1]=1
# A suffix bound is the only new factor inequality after appending a bit.
def go(w,n):
 levels[n]+=1
 for k in range(max(1,n-16),min(12,n-1)+1):sig[(k,w>>(n-k))][n-k]+=1
 if n==28:return
 p[n+1]=p[n];go(w*2,n+1)
 p[n+1]=p[n]+1
 if all(p[n+1]-p[n+1-k]<=p[k] for k in range(1,n+2)):go(w*2+1,n+1)
go(1,1)
groups=defaultdict(list)
for (k,w),s in sig.items():
 if s[1]:groups[tuple(s[1:])].append(format(w,'0'+str(k)+'b'))
coll=[{'words':v,'counts':s} for s,v in groups.items() if len(v)>1]
(L/'word-dfs-results.json').write_text(json.dumps({'prefix_length_max':12,'extension_length_max':16,'total_length_max':28,'level_counts':levels,'collisions':coll},indent=2));print('levels',levels);print('collision_groups',len(coll));print(coll[:12])
