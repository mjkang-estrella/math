import itertools,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);oriented=len(sys.argv)>2
pairs=list(itertools.combinations(range(n),2)) if oriented else [(i,j) for i in range(n) for j in range(n) if i!=j]
counts={k:0 for k in range(2,n)};bad=[];total=0
for code in itertools.product(range(3 if oriented else 2),repeat=len(pairs)):
 G=[set() for _ in range(n)]
 for c,(u,v) in zip(code,pairs):
  if c==1:G[u].add(v)
  elif c==2:G[v].add(u)
 total+=1;dist=[[0 if i==j else 100 for j in range(n)] for i in range(n)]
 for i in range(n):
  for j in G[i]:dist[i][j]=1
 for k in range(n):
  for i in range(n):
   for j in range(n):dist[i][j]=min(dist[i][j],dist[i][k]+dist[k][j])
 for k in counts:
  quasi=True
  def visit(path):
   global quasi
   if len(path)==k+1:
    if path[-1] not in G[path[0]] and path[0] not in G[path[-1]]:quasi=False
    return
   for v in G[path[-1]]:
    if v not in path:visit(path+[v])
  for v in range(n):visit([v])
  if not quasi:continue
  counts[k]+=1;found=False
  for mask in range(1,1<<n):
   S=[i for i in range(n) if mask>>i&1]
   if all(dist[i][j]>=k+1 for i in S for j in S if i!=j) and all(any(dist[i][j]<=k for j in S) for i in range(n) if i not in S):found=True;break
  if not found:bad.append({'k':k,'arcs':[[i,j] for i in range(n) for j in G[i]]})
 if bad:break
out={'n':n,'space':'all labelled oriented graphs' if oriented else 'all labelled loopless digraphs','total':total,'quasi_transitive_counts':counts,'counterexamples':bad}
(D/f'outputs/kernels-{n}-{oriented}.json').write_text(json.dumps(out,indent=2));print(out)
