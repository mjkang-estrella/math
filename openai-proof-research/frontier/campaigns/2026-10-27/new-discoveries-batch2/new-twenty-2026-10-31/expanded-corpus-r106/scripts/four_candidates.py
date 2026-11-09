import itertools,json
out=[]
for chord in [(0,2),(1,3)]:
 E=[(0,1),(1,2),(2,3),(3,0),chord];valid=[]
 for c in itertools.product(range(4),repeat=4):
  if all(c[u]!=c[v] for u,v in E) and c[0]==c[2] and c[1]==c[3]:valid.append(c)
 out.append({'n':4,'chord':chord,'bichromatic_colorings':len(valid)})
for n in range(5,9):
 t=n-4;lower=4+5*t-t*(t-1)//2;out.append({'n':n,'necessary_edge_lower_bound':lower,'triangulated_disk_edges':3*n-7,'impossible_by_degree_sum':lower>3*n-7})
open('outputs/four-candidates-small.json','w').write(json.dumps(out,indent=2));print(out)
