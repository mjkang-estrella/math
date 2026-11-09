import re, ast, pathlib
p=pathlib.Path('source/lean/Closure280.lean')
s=p.read_text(); k=280
nodes=re.findall(r'def node(\d+) : Graph := (\[.*\])',s)
helpers=[]
for n,data in nodes:
 g=ast.literal_eval(data)
 count=sum(sum(v!=0 for v in row)==3 and all(v in (0,2) for v in row) for row in g)
 helpers.append(f'theorem census_node{n} : ((verts node{n}).filter (wye node{n})).length = {count} := by decide +kernel\n')
old=re.search(r'theorem arc_count280.*',s)[0]
new=''.join(helpers)+old.replace('by decide +kernel', 'by\n  simpa only [entries280, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, '+', '.join('census_node'+n for n,_ in nodes)+']')
p.write_text(s.replace(old,new))
