from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
found=[]
for p in (D/'logs').glob('dprime-*-3.log'):
 for line in p.read_text().splitlines():
  try:o=json.loads(line)
  except ValueError:continue
  if 'cycle' in o:found.append(o)
if not found:raise SystemExit('no candidate')
o=min(found,key=lambda x:x['k']);k=o['k'];C=o['cycle'];q=3
# This checker evaluates all original bilinear equations directly; it does not
# call the search neighbor function or accept a spanning-tree certificate.
labels=['1','11','12','21']
for i in range(2,k):labels += [f'{i},{i}',f'{i},{i}p',f'{i},{i+1}',f'{i+1},{i}']
labels=labels[:k]
# Normalize the initial low-coordinate labels to the general notation.
labels=[{'11':'1,1','12':'1,2','21':'2,1'}.get(x,x) for x in labels]
def equations(v,w):
 assert v[0]!=w[0]
 if v[0]:v,w=w,v
 a=dict(zip(labels,v[1]));b=dict(zip(labels,w[1]));r=[]
 r.append((a['1,1']-a['1']+b['1,1']-b['1']+a['1']*b['1'])%q)
 if k>=3:r.append((a['1,2']+a['1,1']+b['1,2']+b['1,1']+a['1']*b['1,1'])%q)
 if k>=4:r.append((a['2,1']+a['1,1']+b['2,1']+b['1,1']+a['1,1']*b['1'])%q)
 for i in range(2,k):
  tests=[(f'{i},{i}',f'{i-1},{i}',1),(f'{i},{i}p',f'{i},{i-1}',0),(f'{i},{i+1}',f'{i},{i}',0),(f'{i+1},{i}',f'{i},{i}p',1)]
  for t,u,typ in tests:
   if t in a:r.append((a[t]+a[u]+b[t]+b[u]+(a[u]*b['1'] if typ else a['1']*b[u]))%q)
 return r
assert all(len(v[1])==k and all(0<=z<q for z in v[1]) for v in C)
assert len({(v[0],tuple(v[1])) for v in C})==len(C)
checks=[equations(C[i],C[(i+1)%len(C)]) for i in range(len(C))]
assert all(len(r)==k-1 and not any(r) for r in checks)
assert len(C)<o['claimed_bound'] and len(C)>=3
out={**o,'direct_equation_residues':checks,'independent_check':'PASS','field':'F3','all_vertices_distinct':True,'source':'2101.06743v1 Definition 2.7 and Conjecture 2.9','qualification':'current source deletes this route; no novelty or campaign eligibility clearance'}
(D/'outputs/dprime-cycle.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({a:v for a,v in out.items() if a not in ['cycle','direct_equation_residues']}))
