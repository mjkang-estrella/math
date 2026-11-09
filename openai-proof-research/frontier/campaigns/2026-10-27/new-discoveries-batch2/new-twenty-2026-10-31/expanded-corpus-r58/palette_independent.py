from pathlib import Path
import itertools,json,collections
O=Path(__file__).resolve().parent
E=list(itertools.combinations(range(5),2)); T=[tuple(E.index(e) for e in itertools.combinations(t,2)) for t in itertools.combinations(range(5),3)]
counts=collections.Counter(); collision_counts=collections.Counter(); leaves=0
# Independent exhaustive depth-first check. No color or vertex symmetry reduction.
def search(a):
 global leaves
 counts[len(a)]+=1
 palettes=[]
 for t in T:
  if max(t)<len(a):
   s=frozenset(a[i] for i in t)
   if s in palettes:collision_counts[len(a)]+=1;return
   palettes.append(s)
 if len(a)==10: leaves+=1;return
 for c in range(4):search(a+[c])
search([])
print(json.dumps({'edges':E,'triangles_edge_indices':T,'nodes_by_depth':dict(counts),'collision_prunes_by_depth':dict(collision_counts),'valid_leaves':leaves,'no_symmetry_reduction':True},indent=2))
