"""Finite diagnostic of a path-disintegration identity, not a mathematical gate.
No files are written. Uses every network on a 3-by-2 grid, including all
32 choices of altered stage-lines. Output is deterministic JSON.
"""
from itertools import permutations,product
from fractions import Fraction
from collections import defaultdict
import json
slots=list(product(range(3),range(2)))
lines=[tuple(i for i,x in enumerate(slots) if x[1]==j) for j in range(2)]
lines += [tuple(i for i,x in enumerate(slots) if x[0]==j) for j in range(3)]
choices=[list(permutations(range(len(L)))) for L in lines]
networks=[]
for coins in product(*choices):
 pos=list(range(6));paths=[pos.copy()]
 for stage in [range(2),range(2,5)]:
  trans=list(range(6))
  for j in stage:
   for i,target in enumerate(coins[j]): trans[lines[j][i]]=lines[j][target]
  pos=[trans[x] for x in pos];paths.append(pos.copy())
 networks.append((coins,paths))
records=0; equal_pairs=0;witness=None
for mask in range(32):
 F=[j for j in range(5) if mask>>j&1]; atoms=defaultdict(list)
 for idx,(coins,paths) in enumerate(networks):
  selected=sorted({a for j in F for a in range(6) if paths[0 if j<2 else 1][a] in lines[j]})
  H=tuple((a,paths[2][a]) for a in selected)
  w=Fraction(1)
  for j in F:
   size=len(choices[j]); weight=2 if coins[j]==tuple(range(len(lines[j]))) else 1
   w*=Fraction(size*weight,size+1)
  atoms[H].append((idx,w))
 for H,rows in atoms.items():
  assert len({w for _,w in rows})==1
  actual={i for i,_ in rows}
  cylinder={i for i,(_,paths) in enumerate(networks) if all(paths[2][a]==v for a,v in H)}
  assert cylinder==actual
  records+=1;equal_pairs+=len(rows)
# Properly limited negative control: revealing only one card does not cover
# a 3-slot altered line, so its local density need not be determined.
partial=defaultdict(list)
for idx,(coins,paths) in enumerate(networks):
 j=0;size=len(choices[j]);weight=2 if coins[j]==tuple(range(3)) else 1
 partial[paths[2][0]].append((idx,Fraction(size*weight,size+1)))
for end,rows in partial.items():
 if len({w for _,w in rows})>1:
  witness={'card':0,'endpoint':end,'density_values':sorted(str(w) for _,w in set(rows))};break
assert witness is not None
witness['density_values']=sorted(set(witness['density_values']))
print(json.dumps({'grid':[3,2],'networks':len(networks),'fault_sets':32,'record_atoms':records,'network_fault_pairs':equal_pairs,'all_full_coverage_cylinder_identities':True,'all_record_density_constants':True,'partial_record_failure':witness,'status':'FINITE DIAGNOSTIC ONLY'},sort_keys=True,indent=2))
