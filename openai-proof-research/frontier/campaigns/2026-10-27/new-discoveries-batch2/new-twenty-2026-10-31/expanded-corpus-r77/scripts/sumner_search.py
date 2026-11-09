import pathlib,itertools as it,json
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
for n in [2,3]:
 N=2*n-2;edges=list(it.combinations(range(N),2));tests=0
 trees=[[(0,1)]] if n==2 else [[(0,1),(1,2)],[(0,1),(0,2)],[(0,2),(1,2)]]
 for mask in range(1<<len(edges)):
  arcs={(u,v) if mask>>i&1 else (v,u) for i,(u,v) in enumerate(edges)}
  for tree in trees:
   for orient in range(1<<len(tree)):
    tes=[(u,v) if orient>>i&1 else (v,u) for i,(u,v) in enumerate(tree)];tests+=1
    assert any(all((f[u],f[v]) in arcs for u,v in tes) for f in it.permutations(range(N),n))
 rows.append(dict(n=n,tournaments=1<<len(edges),tests=tests))
(D/'outputs/search-sumner.json').write_text(json.dumps(dict(id=316026,space='all labeled tournaments on2 and4 vertices; every labeled tree and every edge orientation on2 and3 vertices; n1 source endpoint excluded',rows=rows),indent=2)+'\n')
