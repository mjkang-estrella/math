import json,pathlib
root=pathlib.Path(__file__).resolve().parents[1]
a=json.loads((root/'outputs/four.json').read_text())['result']['labels']
assert sorted(a)==list(range(1,31))
# Reconstruct by component and source names, separately from the search's arrays.
weights={}; edge_labels={}; i=0
for c in range(2):
 for pair in range(3):
  u=(c,'u',pair);v=(c,'v',pair);x=(c,'x',0);y=(c,'x',1)
  for edge in [(u,v),(u,x),(u,y),(v,x),(v,y)]:
   assert frozenset(edge) not in edge_labels
   edge_labels[frozenset(edge)]=a[i];i+=1
vertices=set().union(*edge_labels)
assert len(vertices)==16 and len(edge_labels)==30
for vertex in vertices:
 weights[vertex]=sum(z for e,z in edge_labels.items() if vertex in e)
assert all(len({weights[v] for v in e})==2 for e in edge_labels)
assert set(weights.values())=={45,49,84,99}
out=dict(bijection=True,proper=True,colors=sorted(set(weights.values())),
         vertices=[dict(vertex=list(v),weight=weights[v]) for v in sorted(vertices)])
(root/'outputs/four-verified.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
