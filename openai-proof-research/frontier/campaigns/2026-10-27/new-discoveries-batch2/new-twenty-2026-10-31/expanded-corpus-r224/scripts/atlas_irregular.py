import pathlib,gzip,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
s=gzip.decompress((D/'raw/atlas.dat.gz').read_bytes()).decode().splitlines();graphs=[];j=0
while j<len(s):
 assert s[j].startswith('GRAPH');n=int(s[j+1].split()[1]);j+=2;es=[]
 while j<len(s) and not s[j].startswith('GRAPH'):
  es.append(tuple(map(int,s[j].split())));j+=1
 graphs.append((n,es))
cap=int(sys.argv[1]);total=0;found=0;fail=[];nodes=0
for n,es in graphs:
 if n<2 or len(es)>cap:continue
 seen={0}
 for _ in range(n):
  for u,v in es:
   if u in seen or v in seen:seen.update((u,v))
 if len(seen)<n:continue
 total+=1;m=len(es);deg=[[0]*n for _ in range(4)];groups=[[] for _ in range(4)]
 def dfs(j,used):
  global nodes
  nodes+=1
  if j==m:return all(all(deg[c][u]!=deg[c][v] for u,v in groups[c]) for c in range(used))
  u,v=es[j]
  for c in range(min(used+1,4)):
   deg[c][u]+=1;deg[c][v]+=1;groups[c].append((u,v))
   if dfs(j+1,max(used,c+1)):return True
   groups[c].pop();deg[c][u]-=1;deg[c][v]-=1
  return False
 if dfs(0,0):found+=1
 else:fail.append({'n':n,'edges':es})
print(json.dumps({'atlas_graphs':len(graphs),'order_cap':7,'edge_cap':cap,'connected_tested':total,'four_colorable':found,'unclassified_failures':fail,'nodes':nodes}))
