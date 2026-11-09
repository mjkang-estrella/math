import pathlib,json,itertools as it,collections
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for q in [4,5,7]:
 def add(a,b):return a^b if q==4 else (a+b)%q
 def neg(a):return a if q==4 else -a%q
 def mul(a,b):
  if q!=4:return a*b%q
  c=0
  while b:
   if b&1:c^=a
   a<<=1
   if a&4:a^=7
   b>>=1
  return c
 for k in range(2,7 if q==4 else 5):
  V=list(it.product(range(q),repeat=k));N=len(V);ix={v:i for i,v in enumerate(V)};adj=[[] for _ in range(2*N)]
  for p in V:
   u=ix[p]
   for l1 in range(q):
    l=[l1]
    for i in range(2,k+1):
     if i==2:f=mul(p[0],l1)
     elif i==3:f=mul(p[0],l[1])
     elif i%4 in [0,1]:f=neg(mul(p[i-3],l1))
     else:f=mul(p[0],l[i-3])
     l.append(add(f,neg(p[i-1])))
    v=N+ix[tuple(l)];adj[u].append(v);adj[v].append(u)
  dist=[-1]*(2*N);par=[-1]*(2*N);dist[0]=0;queue=collections.deque([0]);g=10**9
  while queue:
   u=queue.popleft()
   for v in adj[u]:
    if dist[v]<0:dist[v]=dist[u]+1;par[v]=u;queue.append(v)
    elif v!=par[u]:g=min(g,dist[u]+dist[v]+1)
  out.append({'q':q,'k':k,'vertices':2*N,'component_vertices':sum(x>=0 for x in dist),'BFS_girth':g,'claimed':k+5 if k%2 else k+4})
  (D/'outputs/search-367473.json').write_text(json.dumps({'definition':'section6 original signed D(k,q) incidence equations p_i+l_i=f_i; F4=F2[x]/(x^2+x+1)','scope':'q=4 k=2..6; q=5,7 k=2..4; full graph generated, BFS from zero point. Equality to global girth uses source edge-transitivity (not proved by script).','cases':out},indent=2)+'\n')
