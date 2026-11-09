import json,pathlib,hashlib,collections
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166')
j=json.loads((D/'outputs/snakes-exact-11.json').read_text());V=j['vertices'];E=j['edges'];checked=[]
for r in j['outcomes']:
 p=list(range(V));groups=[]
 def f(u):
  while p[u]!=u:u=p[u]
  return u
 assert len(r['tree_edge_indices'])==V-1
 for i in r['tree_edge_indices']:
  u,v,g=E[i];a,b=f(u),f(v);assert a!=b;p[a]=b;groups.append(g)
 assert len(set(groups))==V-1 and r['forbidden'] not in groups and len({f(u) for u in range(V)})==1
 checked.append(r['forbidden'])
print('independent certificate checker verified',len(checked),'trees on',V,'vertices with',len(E),'distinct endpoint/group triples')
(D/'outputs/check.json').write_text(json.dumps({'trees_checked':checked,'vertices':V,'distinct_endpoint_group_edges':len(E),'kernel_checked':False,'source_transport_independently_formalized':False},indent=2))
# Source Example 3 listed 24 edges, with source lexicographic canonical chains/labels.
s=(D/'scripts/snakes.py').read_text().split('# Exact common independent set')[0];import sys;sys.argv=['snakes.py','7'];exec(compile(s,'snakes.py','exec'))
printed=[(11,6,9,6),(6,1,2,6),(2,12,11,6),(12,7,4,6),(5,3,3,6),(3,4,7,6),(9,10,10,6),(10,8,5,6),(12,9,8,7),(9,3,1,7),(2,11,6,7),(1,11,12,6),(7,2,1,6),(4,5,8,6),(8,9,6,6),(10,2,2,7),(8,1,3,7),(11,10,4,7),(3,12,5,7),(6,7,7,7),(4,8,9,7),(1,4,10,7),(5,6,11,7),(7,5,12,7)]
a={(min(u,v)-1,max(u,v)-1,l-1,x) for u,v,l,x in printed};b={(min(u,v),max(u,v),l,x) for u,v,l,x in edges};print('source Example 3 edge match',a==b);assert a==b
