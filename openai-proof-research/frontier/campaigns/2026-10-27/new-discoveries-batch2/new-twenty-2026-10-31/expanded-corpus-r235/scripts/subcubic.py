from pathlib import Path
import itertools,json
D=Path(__file__).resolve().parents[1]
def color(edges,n,a,b):
 m=len(edges);adj=[[False]*m for _ in edges];near=[[False]*m for _ in edges]
 for i,e in enumerate(edges):
  for j,f in enumerate(edges):
   adj[i][j]=i!=j and bool(set(e)&set(f))
 for i in range(m):
  for j in range(m):near[i][j]=i!=j and (adj[i][j] or any(adj[i][k] and adj[k][j] for k in range(m)))
 colors=[-1]*m
 def dfs(done,used1,used2):
  if done==m:return True
  available={i:[c for c in range(a+b) if all(colors[j]!=c or not (adj[i][j] if c<a else near[i][j]) for j in range(m)) and (c<a and c<=used1 or c>=a and c-a<=used2)] for i in range(m) if colors[i]<0}
  i=min(available,key=lambda j:len(available[j]))
  for c in available[i]:
   colors[i]=c
   if dfs(done+1,max(used1,c+1) if c<a else used1,max(used2,c-a+1) if c>=a else used2):return True
  colors[i]=-1;return False
 return dfs(0,0,0)
out=[]
for n in range(2,7):
 pairs=list(itertools.combinations(range(n),2));count=0;fails=[]
 for mask in range(1<<len(pairs)):
  es=[e for j,e in enumerate(pairs) if mask>>j&1];deg=[sum(i in e for e in es) for i in range(n)]
  if max(deg,default=0)>3:continue
  # On <=6 vertices, the only subcubic nonplanar simple graph is K3,3.
  if n==6 and len(es)==9 and any(all(((i,j) in es or (j,i) in es)==((i in S)!=(j in S)) for i,j in pairs) for S in map(set,itertools.combinations(range(n),3))):continue
  count+=1
  for a,b in [(1,6),(2,3)]:
   if not color(es,n,a,b):fails.append({'edges':es,'a':a,'b':b})
 row={'n':n,'labeled_subcubic_planar_graphs':count,'failures':fails};print(row,flush=True);out.append(row)
(D/'subcubic-search.json').write_text(json.dumps(out,indent=2)+'\n')
