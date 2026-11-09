from pathlib import Path
from itertools import combinations
import json
r=Path(__file__).resolve().parents[1]
def refine(A,cells):
 while True:
  new=[]
  for cell in cells:
   buckets={}
   for v in cell:
    key=tuple(sum(A[v][w] for w in c) for c in cells);buckets.setdefault(key,[]).append(v)
   new.extend(tuple(buckets[k]) for k in sorted(buckets))
  if new==cells:return new
  cells=new
def canon(A):
 n=len(A)
 def walk(cells):
  cells=refine(A,cells)
  if all(len(c)==1 for c in cells):
   p=tuple(c[0] for c in cells);return tuple(A[i][j] for i in p for j in p),p
  t=next(i for i,c in enumerate(cells) if len(c)>1);cell=cells[t]
  return min(walk(cells[:t]+[(v,),tuple(w for w in cell if w!=v)]+cells[t+1:]) for v in cell)
 return walk([tuple(range(n))])
def encode(flat):return sum(x<<i for i,x in enumerate(flat))
graphs=[(0,)];levels=[{'order':1,'graphs':[0],'extensions':[]}]
for n in range(1,8):
 records=[];nxt=set()
 for idx,flat in enumerate(graphs):
  A=[list(flat[i*n:(i+1)*n]) for i in range(n)];avail=[i for i,row in enumerate(A) if sum(row)<3]
  for k in range(1,min(3,len(avail))+1):
   for ns in combinations(avail,k):
    B=tuple(tuple(row+[int(i in ns)]) for i,row in enumerate(A))+(tuple(int(i in ns) for i in range(n))+(0,),)
    bflat=tuple(x for row in B for x in row);canonical,p=canon(B);nxt.add(canonical)
    records.append({'source_index':idx,'neighbors':sum(1<<i for i in ns),'extension':encode(bflat),'target_flat':canonical,'permutation':p})
 graphs=sorted(nxt);lookup={g:i for i,g in enumerate(graphs)}
 for c in records:c['target_index']=lookup[c.pop('target_flat')]
 levels.append({'order':n+1,'graphs':[encode(g) for g in graphs],'extensions':records})
 print(n+1,len(graphs),len(records),flush=True)
assert [len(x['graphs']) for x in levels]==[1,1,2,6,10,29,64,194]
(r/'graph-extensions.json').write_text(json.dumps({'levels':levels},indent=2)+'\n')
# Kernel replay checks explicit isomorphisms; no canonicalization is trusted by Lean.
mods=[]
for level in levels[1:]:
 n=level['order'];cs=level['extensions']
 for start in range(0,len(cs),100):
  name=f'GraphExtensions{n}_{start//100:03d}';mods.append(name)
  rows=[]
  for c in cs[start:start+100]:
   rows.append(f'({c["extension"]}, {level["graphs"][c["target_index"]]}, ['+', '.join(map(str,c['permutation']))+'])')
  lines=['import GraphChecker',f'namespace Nut8.{name}',f'def data : List (Nat × Nat × List Nat) := [',',\n'.join(rows),']',f'theorem checked : data.all (fun c => graphIsoCheck {n} c.1 c.2.1 c.2.2) = true := by','  decide +kernel',f'end Nut8.{name}']
  (r/'formal'/(name+'.lean')).write_text('\n'.join(lines)+'\n')
(r/'graph-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
