import json,pathlib,itertools
rows=[json.loads(x) for x in pathlib.Path(__file__).with_name('circulants.log').read_text().splitlines()];checked=0;paths=0;counts={}
for r in rows:
 if 'status' not in r:continue
 counts[r['status']]=counts.get(r['status'],0)+1
 if not r.get('order'):continue
 n=r['n'];a,b,m=r['jumps'];order=r['order'];pos={v:i for i,v in enumerate(order)};assert sorted(order)==list(range(n))
 def adjacent(x,y):return (x-y)%n in {a,b,m,n-a,n-b}
 forward={v:[w for w in range(n) if pos[w]>pos[v] and adjacent(v,w)] for v in range(n)}
 def dfs(path):
  global paths
  paths+=1
  if len(path)>=4 and adjacent(path[0],path[-1]):assert all(adjacent(x,y) for x,y in itertools.combinations(path,2)),(r,path)
  for v in forward[path[-1]]:dfs(path+[v])
 for v in range(n):dfs([v])
 checked+=1
print(json.dumps({'completed_graph_rows':sum(counts.values()),'statuses':counts,'successful_orders_independently_checked':checked,'all_directed_paths_visited':paths,'failure':False}),flush=True)
