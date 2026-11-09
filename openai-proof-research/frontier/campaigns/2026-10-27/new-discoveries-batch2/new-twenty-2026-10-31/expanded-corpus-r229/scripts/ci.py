import itertools,random,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def inverse(a,n):
 a=[a[i]|(1<<(n+i)) for i in range(n)]
 for j in range(n):
  p=next((i for i in range(j,n) if a[i]>>j&1),None)
  if p is None:return
  a[j],a[p]=a[p],a[j]
  for i in range(n):
   if i!=j and a[i]>>j&1:a[i]^=a[j]
 return [x>>n for x in a]
def matching(adj,n):
 match={}
 def aug(i,seen):
  for j in range(n):
   if adj[i]>>j&1 and j not in seen:
    seen.add(j)
    if j not in match or aug(match[j],seen):match[j]=i;return True
  return False
 return all(aug(i,set()) for i in range(n))
def cost(a,b,n):
 g=[0]*(2*n)
 for i in range(n):
  for j in range(n):
   if a[j]>>i&1:g[i]|=1<<(n+j)
   if b[i]>>j&1:g[n+j]|=1<<i
 dist=[]
 for u in range(2*n):
  row=[999]*(2*n);row[u]=0;q=[u]
  for v in q:
   for w in range(2*n):
    if g[v]>>w&1 and row[w]==999:row[w]=row[v]+1;q.append(w)
  dist.append(row)
 for c in range(1,2*n,2):
  adj=[sum(1<<j for j in range(n) if max(dist[i][n+j],dist[n+j][i])<=c) for i in range(n)]
  if matching(adj,n):return c
 raise AssertionError('reachability failure')
rng=random.Random(229);out=[]
for n in range(1,9):
 counts={};inv=0;trials=1<<(n*n) if n<=4 else 4000
 for k in range(trials):
  a=[(k>>(n*i))&((1<<n)-1) for i in range(n)] if n<=4 else [sum(1<<j for j in range(n) if rng.random()<rng.choice([.2,.35,.5])) for i in range(n)]
  b=inverse(a,n)
  if b is None:continue
  inv+=1;c=cost(a,b,n);counts[c]=counts.get(c,0)+1
  if c>3:print('c>3 witness',n,a,b,c,flush=True)
 row={'n':n,'matrix_trials':trials,'invertible':inv,'minimum_odd_weakening_histogram':counts,'exhaustive':n<=4};out.append(row);print(row,flush=True)
(D/'evidence/ci-search.json').write_text(json.dumps(out,indent=2))
