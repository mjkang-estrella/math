import json,itertools,pathlib
D=pathlib.Path(__file__).resolve().parents[1];c=json.loads((D/'outputs/johnson-certificate.json').read_text());vertices=[sum(1<<i for i in s)for s in itertools.combinations(range(8),4)];bags=list(map(set,c['bags']));edges=[(u,v)for u,v in itertools.combinations(vertices,2)if (u^v).bit_count()==2]
assert len(vertices)==70 and len(edges)==560 and len(bags)==70
assert set.union(*bags)==set(vertices)
assert all(any(u in b and v in b for b in bags)for u,v in edges)
for v in vertices:
 where=[i for i,b in enumerate(bags)if v in b];assert where==list(range(min(where),max(where)+1))
assert max(map(len,bags))==41
out=dict(vertices=70,edges=560,bags=70,max_bag_size=41,width_upper_bound=40,source_conjectured_value=43,all_cover_edge_interval_checks=True,ordinary_refutation='tw <= pw <= 40 < 43; no exact treewidth/pathwidth lower bound proved here',prior_status='Known numerical value in Coudert–Mazauric–Nisse 2014 Table 15 p.47; excluded')
(D/'outputs/johnson-independent-check.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
