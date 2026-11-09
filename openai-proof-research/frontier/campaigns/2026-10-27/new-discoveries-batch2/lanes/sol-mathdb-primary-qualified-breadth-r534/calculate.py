from pathlib import Path
import json
out=[]
for l in range(2,13):
 lim=1<<(l+1);reducible=set();parts={a:[1|(1<<a)|(s<<1) for s in range(1<<(a-1))] for a in range(1,l+1)}
 for a in range(1,l):
  for b in range(a,l-a+1):
   for x in parts[a]:
    shifts=[i for i in range(a+1) if x>>i&1]
    for y in parts[b]:
     z=0
     for i in shifts:z|=y<<i
     reducible.add(z)
 count=0;bad=[]
 for h in range(1,lim,2):
  elems=[i for i in range(1,l+1) if h>>i&1]
  if any(not (h>>(i+j)&1) for i in elems for j in elems if i+j<=l):continue
  count+=1;counts=[0]*(l+2);s=h
  while s:
   if s!=1 and s&1 and s not in reducible:counts[s.bit_count()]+=1
   s=(s-1)&h
  # Source compares indices 0 through l; also record full through l+1.
  down=False;unimodal=True
  for x,y in zip(counts[:l+1],counts[1:l+1]):
   if y<x:down=True
   if down and y>x:unimodal=False
  if not unimodal:bad.append(dict(prefix=elems,counts=counts))
 out.append(dict(l=l,closed_prefixes=count,counterexamples=bad))
 if bad:break
p=Path(__file__).parent/'bounded-calculation.json';p.write_text(json.dumps(dict(scope='Exhaustive additive-closed prefixes H intersect [0,l], extended by all integers >l; sumset atoms; source indices 0..l only. Finite evidence, not all-l proof.',results=out),indent=2)+'\n');print(p.read_text())
