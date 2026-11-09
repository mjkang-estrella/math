import pathlib,json,itertools,functools
D=pathlib.Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def rooted(n):
 if n==1:return ((),)
 pool=sorted(t for k in range(1,n) for t in rooted(k));out=[]
 def rec(start,left,parts):
  if not left:out.append(tuple(parts));return
  for i in range(start,len(pool)):
   k=sz(pool[i])
   if k<=left:rec(i,left-k,parts+[pool[i]])
 rec(0,n-1,[]);return tuple(out)
@functools.lru_cache(None)
def sz(t):return 1+sum(map(sz,t))
def graph(t):
 adj=[];parents=[]
 def go(s,par):
  v=len(adj);adj.append([]);parents.append(par)
  if par>=0:adj[v].append(par);adj[par].append(v)
  for c in s:go(c,v)
 go(t,-1);return adj,parents
def encode(adj,v,p):return tuple(sorted(encode(adj,u,v) for u in adj[v] if u!=p))
rows=[];hits=[]
for n in range(14,15):
 seen=set();cnt=0;orient=0
 for t in rooted(n):
  adj,par=graph(t);key=min(encode(adj,v,-1) for v in range(n))
  if key in seen:continue
  seen.add(key);cnt+=1
  ds=[]
  for r in range(n):
   dist=[-1]*n;dist[r]=0;todo=[r]
   for v in todo:
    for u in adj[v]:
     if dist[u]<0:dist[u]=dist[v]+1;todo.append(u)
   ds.append(dist)
  best=-1;bad=[];opt=0
  for mask in range(1<<(n-2)):
   x=[0]*n
   for v in range(1,n):x[v]=x[par[v]]+(1 if v==1 or mask>>(v-2)&1 else -1)
   score=n*sum(a*a for a in x)-sum(x)**2;orient+=1
   if score<best:continue
   ok=any(all(abs(x[v]-x[r])==ds[r][v] for v in range(n)) and (max(map(len,adj))<=2 or len(adj[r])>=3) for r in range(n))
   if score>best:best=score;bad=[];opt=0
   opt+=1
   if not ok:bad.append(x)
  if bad:
   h={'n':n,'tree':t,'adj':adj,'variance_numerator':best,'optimizer':bad[0],'optimal_orientations_half':opt};hits.append(h);print('HIT',h,flush=True)
  if hits:break
 rows.append({'n':n,'free_trees':cnt,'orientations_mod_sign':orient});print(rows[-1],flush=True)
 if hits:break
(D/'outputs/variance14.json').write_text(json.dumps({'rows':rows,'hits':hits},indent=2))
