import re,ast,pathlib
for k in range(281,582):
 p=pathlib.Path(f'source/lean/Closure{k:03}.lean');s=p.read_text()
 nodes=re.findall(r'def node(\d+) : Graph := (\[.*\])',s)
 helpers=[]
 for n,data in nodes:
  g=ast.literal_eval(data)
  count=sum(sum(v!=0 for v in row)==3 and all(v in (0,2) for v in row) for row in g)
  helpers.append(f'theorem census_node{n} : ((verts node{n}).filter (wye node{n})).length = {count} := by decide +kernel\n')
 old=re.search(r'theorem arc_count\d+.*',s)[0]
 new=''.join(helpers)+old.replace('by decide +kernel',f'by\n  simp only [entries{k}, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, '+', '.join('census_node'+n for n,_ in nodes)+']\n  decide +kernel')
 p.write_text(s.replace(old,new))
