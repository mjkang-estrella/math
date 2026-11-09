import pathlib,json,importlib.util,random,time,math
P=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('circle_geometry',P/'scripts/circles.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
row=next(r for r in json.loads((P/'inputs/circle-search.json').read_text()) if r['status']=='node_limit')
normals,adj=mod.arrangement(row['n'],row['normals']);n=len(adj);rng=random.Random(23318);start=time.monotonic();best=n
for restart in range(30):
 colors=[rng.randrange(3) for _ in range(n)];counts=[[0]*3 for _ in range(n)]
 for v in range(n):
  for u in adj[v]:counts[v][colors[u]]+=1
 for step in range(100000):
  bad=[v for v in range(n) if counts[v][colors[v]]]
  if not bad:
   assert all(colors[u]!=colors[v] for u in range(n) for v in adj[u])
   result={'n':row['n'],'sample':row['sample'],'status':'3-colorable','restart':restart,'step':step,'normals':normals,'colors':colors,'seconds':time.monotonic()-start}
   (P/'inputs/circle-hard-coloring.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ['normals','colors']}));raise SystemExit
  v=rng.choice(bad);old=colors[v];choices=[c for c in range(3) if c!=old]
  c=min(choices,key=lambda c:counts[v][c]+rng.random()*0.2)
  delta=counts[v][c]-counts[v][old]
  temp=0.05+0.8*(1-(step%10000)/10000)
  if delta<=0 or rng.random()<math.exp(-delta/temp):
   colors[v]=c
   for u in adj[v]:counts[u][old]-=1;counts[u][c]+=1
 print('restart',restart,'bad_vertices',len(bad),flush=True)
print('No coloring found; not an uncolorability proof')
