from pathlib import Path
from itertools import combinations
import sys,json,time
n=int(sys.argv[1]); branch=int(sys.argv[2]); pairs=list(combinations(range(n),2)); N=1<<n; full=N-1
out=[0]*n; indeg=[0]*n; spectra=[0]*(1<<len(pairs)); counts=[0]*len(spectra)
# Test every subset in cardinality order; in an asymmetric loopless digraph
# fewer than three selected vertices cannot dominate themselves.
subs=[sum(1<<v for v in s) for k in range(3,n+1) for s in combinations(range(n),k)]
vertices=[[v for v in range(n) if s>>v&1] for s in subs]
ks=[s.bit_count() for s in subs]
def visit(i,g):
 if i==len(pairs):
  if 0 in indeg: return
  for vs,k in zip(vertices,ks):
   covered=0
   for v in vs: covered |= out[v]
   if covered==full: break
  else: raise AssertionError('valid without TD')
  spectra[g]|=1<<k; counts[g]+=1; return
 a,b=pairs[i]; choices=range(3) if i else [branch]
 for choice in choices:
  if choice==0: visit(i+1,g)
  else:
   u,v=(a,b) if choice==1 else (b,a)
   out[u]|=1<<v; indeg[v]+=1
   visit(i+1,g|(1<<i))
   out[u]^=1<<v; indeg[v]-=1
visit(0,0)
p=Path('recomputed'); p.mkdir(exist_ok=True)
(p/f'n{n}-branch{branch}.json').write_text(json.dumps(dict(n=n,branch=branch,spectra=spectra,counts=counts)))
print(n,branch,sum(c>0 for c in counts),sum(counts),flush=True)
