from pathlib import Path
import itertools,json,runpy,math
L=Path(__file__).resolve().parent;d=runpy.run_path(str(L/'checks.py'))
profiles=d['graphs']()['profiles']
import ast
assert all((lambda z:z[0]==sum(z[1:]))(ast.literal_eval(k)) for k in profiles)
lefts=[[(1,2,3)],[(1,2,2),(0,2,3)]]
rights={ (0,0):[(1,2,3)],(0,1):[(1,2,2),(0,2,3)],(1,0):[(1,2,1),(1,0,3)],(1,1):[(1,2,2),(0,2,1)]}
tested=0
for ls in itertools.combinations(range(1,4),2):
 for rs in itertools.combinations(range(1,4),2):
  edges=list(itertools.product(ls,rs))
  for mask in range(16):
   E={e for i,e in enumerate(edges) if mask>>i&1}
   if {a for a,b in E}!=set(ls) or {b for a,b in E}!=set(rs):continue
   for j,k in itertools.product(range(2),repeat=2):
    images=[]
    for a in lefts[k]:
     for b in rights[j,k]:
      F=d['image'](E,a,b)
      if len({x for x,y in F})>1 and len({y for x,y in F})>1:images.append(F)
    assert len(images)==1 and d['mult'](images[0])==d['mult'](E)
    tested+=1
residual=[(a,b,96-a-b) for a in range(1,21) for b in range(1,39) if 1<=96-a-b<=57]
out=dict(full_projection_conservation_graphs=sum(profiles.values()),two_by_two_graph_regime_cases=tested,cover_exact_cover=dict(variables=math.factorial(9),constraints=math.factorial(9)//math.factorial(2),ones_per_column=math.comb(9,7),required_selected=math.factorial(7)),BHR_v97_threshold_residual_count=len(residual),note='Residuals exclude only the cited threshold theorem; no assertion that other constructions fail.')
(L/'structural.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
