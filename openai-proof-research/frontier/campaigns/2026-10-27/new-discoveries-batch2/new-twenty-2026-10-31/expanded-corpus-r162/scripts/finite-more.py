import pathlib,json,itertools,random,time
D=pathlib.Path(__file__).resolve().parents[1];out={}
# Correctly keep the sharp-LKS formulation defect separate from planar dynamic coloring.
exec((D/'scripts/graph-search.py').read_text().split('for n in range(2,7):')[0])
out={}
n=6;pairs=list(itertools.combinations(range(n),2));planar=0;fail=[]
for mask in range(1<<15):
 a=[0]*n
 for j,(u,v) in enumerate(pairs):
  if mask>>j&1:a[u]|=1<<v;a[v]|=1<<u
 nonplanar=any(all(a[u]>>v&1 for u,v in itertools.combinations(vs,2)) for vs in itertools.combinations(range(n),5))
 if not nonplanar:
  for u,v in pairs:
   if not a[u]>>v&1:continue
   other=[x for x in range(n) if x not in [u,v]]
   if all(a[x]>>y&1 for x,y in itertools.combinations(other,2)) and all((a[u]|a[v])>>x&1 for x in other):nonplanar=True;break
 if not nonplanar:
  for s in itertools.combinations(range(n),3):
   if all(a[u]>>v&1 for u in s for v in range(n) if v not in s):nonplanar=True;break
 if nonplanar:continue
 planar+=1
 ok=False
 for u,v in pairs:
  if a[u]>>v&1:continue
  f=list(range(n));f[v]=u
  if all(len({f[w] for w in range(n) if a[x]>>w&1})>=min(2,a[x].bit_count()) for x in range(n)):ok=True;break
 if not ok:fail.append(mask)
out['343781']={'n':6,'all_labeled_graphs':32768,'planar_graphs':planar,'failures':fail}
print(out,flush=True)
# Exact edge-order backtracking on complete equipartite graphs; small instances only.
def ordering(n,s,k,cyclic):
 edges=[(i,j) for i in range(n*s) for j in range(i+1,n*s) if i//n!=j//n];m=len(edges)
 masks=[(1<<i)|(1<<j) for i,j in edges];nodes=0;cut=False;deadline=time.monotonic()+8
 path=[0]
 def dfs(used):
  nonlocal nodes,cut
  nodes+=1
  if nodes%1024==0 and time.monotonic()>deadline:cut=True;return False
  if len(path)==m:
   return not cyclic or all(not(masks[path[i]]&masks[path[j]]) for i in range(m-k+1,m) for j in range(k-1) if (j-i)%m<k)
  recent=0
  for j in path[-(k-1):] if k>1 else []:recent|=masks[j]
  for j in range(m):
   if used>>j&1 or masks[j]&recent:continue
   if cyclic and len(path)>=m-k+2:
    if any(masks[j]&masks[path[t]] for t in range(len(path)+k-m)):continue
   path.append(j)
   if dfs(used|1<<j):return True
   path.pop()
   if cut:return False
  return False
 ok=dfs(1)
 return {'n':n,'s':s,'window':k,'cyclic':cyclic,'found':ok,'exhausted':not cut and not ok,'completed_without_cutoff':not cut,'nodes':nodes,'edge_order':[edges[j] for j in path] if ok else None}
res=[]
for n,s in [(2,2),(2,3),(3,2),(2,4),(3,3)]:
 for k in [n*s//2-1,n*s//2]:
  for cyc in [False,True]:
   row=ordering(n,s,k,cyc);res.append(row);print('matching', {a:b for a,b in row.items() if a!='edge_order'},flush=True)
   out['342666']=res;(D/'outputs/finite-more.json').write_text(json.dumps(out,indent=2))
