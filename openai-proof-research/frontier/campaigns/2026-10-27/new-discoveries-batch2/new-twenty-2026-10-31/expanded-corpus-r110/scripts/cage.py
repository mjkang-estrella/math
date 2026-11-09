import itertools,json
# Exact induced-path enumeration on two classical cages; not a large-g test.
for name,n,E in [('Petersen',10,[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)]),('Heawood',14,[(i,(i+1)%14) for i in range(14)]+[(i,(i+[5,-5][i%2])%14) for i in range(0,14,2)])]:
 adj=[0]*n
 for u,v in E:adj[u]|=1<<v;adj[v]|=1<<u
 forbidden=set();paths=0
 def dfs(v,mask,p):
  global paths
  paths+=1
  if len(p)>=3:forbidden.update(sum(1<<j for j in S) for S in itertools.combinations(p,3))
  choices=adj[v]&~mask
  while choices:
   z=choices&-choices;choices-=z;w=z.bit_length()-1
   if adj[w]&mask==1<<v:dfs(w,mask|z,p+[w])
 for v in range(n):dfs(v,1<<v,[v])
 for k in range(n,1,-1):
  found=None
  for S in itertools.combinations(range(n),k):
   if all(sum(1<<i for i in T) not in forbidden for T in itertools.combinations(S,3)):found=S;break
  if found is not None:break
 print(json.dumps(dict(name=name,n=n,degree=[a.bit_count() for a in adj],oriented_induced_paths=paths,forbidden_triples=len(forbidden),mp=k,maximum_set=found)),flush=True)
