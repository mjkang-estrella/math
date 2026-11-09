from pathlib import Path
import itertools,collections,json,hashlib
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-review-r1')
cs=[(i,) for i in range(5)]+list(itertools.combinations(range(5),2))
G={sum(1<<i for i,c in enumerate(cs) if all(x>>v&1 for v in c)) for x in range(32)}
# Elbracht--Kneip--Teegen Section 4 dependency graph, restricted to the constant=1 face.
# Good-good edges strictly decrease inclusion, since G is meet closed.
N=1<<15;out=[set() for _ in range(N)];indeg=[0]*N
for a in range(N):
 if a in G:continue
 for c in G:
  b=a|c;e=a&c
  if b not in G and e not in G:
   for z in [b,e]:
    if z!=a:out[a].add(z)
 for z in out[a]:indeg[z]+=1
Q=collections.deque(i for i in range(N) if not indeg[i]);seen=0
while Q:
 a=Q.popleft();seen+=1
 for z in out[a]:
  indeg[z]-=1
  if indeg[z]==0:Q.append(z)
print('Dependency graph vertices',N,'edges',sum(map(len,out)),'topologically removed',seen,'acyclic',seen==N)
(L/'subsumption-receipt.json').write_text(json.dumps({'graph_vertices':N,'edges':sum(map(len,out)),'acyclic':seen==N,'known_cycle_criterion_applies':seen!=N},indent=2))
for name in ['cites-W2913322957','cites-W4280572229']:
 a=json.loads((L/'downloads'/name/'body').read_text());print(name,'count',a['meta']['count'])
 for p in a['results']:print(p['title'],p.get('doi'),p['publication_date'])
a=json.loads((L/'downloads/pool-head/body').read_text());print('Lean Pool HEAD',a['sha'],a['commit']['committer']['date'])
for p in json.loads((L/'downloads/pool-candidates/body').read_text()):print('Pool candidate',p['path'])
for p in sorted((L/'downloads').glob('github-query-*/body')):
 a=json.loads(p.read_text());print(p.parent.name,a.get('total_count'),[i['full_name'] for i in a.get('items',[])])
# Explicit DFS cycle among the Kahn residual; keep the witnessing good c for each edge.
if seen!=N:
 color=[0]*N;par={};cycle=None
 for start in range(N):
  if not indeg[start] or color[start]:continue
  color[start]=1;stack=[(start,iter(sorted(out[start])))]
  while stack and cycle is None:
   a,it=stack[-1]
   try:b=next(it)
   except StopIteration:color[a]=2;stack.pop();continue
   if not indeg[b]:continue
   if color[b]==0:color[b]=1;par[b]=a;stack.append((b,iter(sorted(out[b]))))
   elif color[b]==1:
    chain=[a]
    while chain[-1]!=b:chain.append(par[chain[-1]])
    cycle=list(reversed(chain));break
  if cycle:break
 assert cycle
 edges=[]
 for a,b in zip(cycle,cycle[1:]+cycle[:1]):
  c=next(c for c in sorted(G) if a|c not in G and a&c not in G and b in [a|c,a&c])
  edges.append({'a':a,'b':b,'c_good':c,'meet':a&c,'join':a|c});assert a not in G and b not in G and c in G
 print('Known-criterion explicit cycle',edges)
 (L/'known-criterion-cycle.json').write_text(json.dumps(edges,indent=2))
