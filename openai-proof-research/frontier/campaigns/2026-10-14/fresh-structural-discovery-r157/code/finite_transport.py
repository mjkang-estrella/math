# Bounded exact poset-automorphism comparisons, using saved diagnostic only.
from pathlib import Path
from itertools import permutations,product
import json,time
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r157');j=json.loads((R/'receipts/finite-bmp.json').read_text());start=time.monotonic()
V=[tuple(v) for v in j['vertices']]
def ell(w):return sum(w[i]>w[k] for i in range(4) for k in range(i+1,4))
def le(a,b):return all(sorted(a[:i])[k]<=sorted(b[:i])[k] for i in range(1,5) for k in range(i))
out=[]
for x in [(1,2,3,4),(1,3,2,4)]:
 vs=[v for v in V if le(x,v)];levels=[[v for v in vs if ell(v)==d] for d in range(ell(x),5)];n=0;comparisons=0;bad=[]
 rr=[r for r in j['subset_results'] if tuple(r['x'])==x];lookup={frozenset(map(tuple,r['F'])):r for r in rr}
 for ps in product(*(permutations(L) for L in levels)):
  mp={a:b for L,p in zip(levels,ps) for a,b in zip(L,p)}
  if not all(le(a,b)==le(mp[a],mp[b]) for a in vs for b in vs):continue
  n+=1
  for F,r in lookup.items():
   target=lookup[frozenset(mp[y] for y in F)];comparisons+=1
   if r['dims_degrees0to5']!=target['dims_degrees0to5'] or r['minimal_generators_degrees0to5']!=target['minimal_generators_degrees0to5']:bad.append([list(F),[mp[y] for y in F]])
  if time.monotonic()-start>45:raise RuntimeError('bounded automorphism comparison exceeded')
 out.append({'bottom':x,'interval_vertices':len(vs),'automorphisms':n,'subset_comparisons':comparisons,'mismatches':bad})
(R/'receipts/finite-transport.json').write_text(json.dumps({'scope':'Only self-isomorphisms of two fixed S4 intervals, degrees0..5. No cross-system invariance conclusion.','results':out,'elapsed':time.monotonic()-start},indent=2)+'\n');print(json.dumps(out))
