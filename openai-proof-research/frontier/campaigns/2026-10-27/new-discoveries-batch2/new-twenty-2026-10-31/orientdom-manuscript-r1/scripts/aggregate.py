from pathlib import Path
from itertools import combinations
import json,hashlib
R=Path.cwd(); orders=[]; allrows={}
for n in range(3,7):
 pairs=list(combinations(range(n),2)); L=1<<len(pairs); spectra=[0]*L; counts=[0]*L
 for b in range(3):
  d=json.loads((R/f'recomputed/n{n}-branch{b}.json').read_text())
  for g in range(L): spectra[g]|=d['spectra'][g]; counts[g]+=d['counts'][g]
 rows=[]; connected_graphs=connected_orientations=gaps=0
 for g in range(L):
  if not counts[g]: continue
  s=[k for k in range(n+1) if spectra[g]>>k&1]; assert s
  gaps+=int(s!=list(range(s[0],s[-1]+1)))
  seen=1
  while True:
   new=seen
   for i,(a,b) in enumerate(pairs):
    if g>>i&1:
     if seen>>a&1: new|=1<<b
     if seen>>b&1: new|=1<<a
   if new==seen: break
   seen=new
  connected=seen==(1<<n)-1
  connected_graphs+=int(connected); connected_orientations+=counts[g] if connected else 0
  rows.append(dict(edge_mask=g,spectrum=s,orientations=counts[g],connected=connected))
 allrows[str(n)]=dict(vertex_labels=list(range(n)),pair_order=pairs,graphs=rows)
 orders.append(dict(n=n,graphs=len(rows),orientations=sum(counts),gaps=gaps,connected_graphs=connected_graphs,connected_orientations=connected_orientations))
expected=[(1,2,1,2),(22,122,22,122),(603,16168,603,16168),(25418,5545708,25408,5545668)]
assert [(d['graphs'],d['orientations'],d['connected_graphs'],d['connected_orientations']) for d in orders]==expected
assert all(d['gaps']==0 for d in orders)
# Independent all-subset TD routine for printed examples (no cardinality shortcut).
def gamma(n,arcs):
 valid=all(any(v==b for a,b in arcs) for v in range(n))
 if not valid: return None
 return min(s.bit_count() for s in range(1<<n) if all(any((s>>a)&1 and v==b for a,b in arcs) for v in range(n)))
cycles=[]
for n in [3,4,5]:
 arcs=[(i,(i+1)%n) for i in range(n)]; rev=[(b,a) for a,b in arcs]
 flips=[]
 for i,(a,b) in enumerate(arcs): flips.append(gamma(n,arcs[:i]+[(b,a)]+arcs[i+1:]))
 values=[gamma(n,arcs),gamma(n,rev)]; assert values==[n,n] and flips==[None]*n
 cycles.append(dict(n=n,arcs=arcs,reversed_arcs=rev,gamma=values,disagreement=len(set(arcs)-set(rev)),single_flip_gamma=flips))
(R/'recomputed/spectra.json').write_text(json.dumps(allrows,separators=(',',':'))+'\n')
ver=dict(status='PASS',orders=orders,cycle_examples=cycles,comparison='Matches review all-graph counts and discovery connected counts; no gaps.',scope='Every labeled simple graph and every orientation, orders 3 through 6; isolated Python, fresh computation.')
(R/'recomputed/verification.json').write_text(json.dumps(ver,indent=2)+'\n'); print(json.dumps(ver,indent=2))
