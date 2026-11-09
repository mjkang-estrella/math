import pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(11,14):
 rays=set();leaves=0;nodes=0
 def dfs(r,cols,diag):
  global leaves,nodes
  nodes+=1
  if r==n:rays.add(diag);leaves+=1;return
  for c in range(n):
   dc=1<<(n-1+r-c)
   if not cols>>c&1 and not diag&dc:dfs(r+1,cols|1<<c,diag|dc)
 dfs(0,0,0)
 def scores(pos,prev,s):
  if pos==n:return int(s==n*(n-1)//2)
  return sum(scores(pos+1,x,s+x) for x in range(prev,n) if (pos+1)*pos//2<=s+x<=n*(n-1)//2 and s+x+(n-pos-1)*(n-1)>=n*(n-1)//2)
 row={'n':n,'binary_xrays':len(rays),'score_sequences_Landau':scores(0,0,0),'permutations_with_distinct_diagonals':leaves,'dfs_nodes':nodes};out.append(row);print(row,flush=True)
 (D/'outputs/xray-search-extended.json').write_text(json.dumps(out,indent=2))
