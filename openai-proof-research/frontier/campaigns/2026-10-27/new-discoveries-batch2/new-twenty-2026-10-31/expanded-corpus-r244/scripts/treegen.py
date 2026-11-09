def canonical(adj):
 n=len(adj);degree=[len(s) for s in adj];leaves=[v for v in range(n) if degree[v]<=1];remain=n
 while remain>2:
  remain-=len(leaves);new=[]
  for u in leaves:
   degree[u]=0
   for v in adj[u]:
    if degree[v]:
     degree[v]-=1
     if degree[v]==1:new.append(v)
  leaves=new
 def rooted(u,p):return '('+''.join(sorted(rooted(v,u) for v in adj[u] if v!=p))+')'
 return min(rooted(u,-1) for u in leaves)
def trees(stop):
 cur=[(frozenset([1]),frozenset([0]))]
 yield 2,cur
 for n in range(3,stop+1):
  out={}
  for a in cur:
   for u in range(n-1):
    b=list(a);b[u]=b[u]|{n-1};b.append(frozenset([u]));out.setdefault(canonical(b),tuple(b))
  cur=list(out.values());yield n,cur
def distances(a):
 out=[]
 for u in range(len(a)):
  ds=[-1]*len(a);ds[u]=0;q=[u]
  for v in q:
   for w in a[v]:
    if ds[w]<0:ds[w]=ds[v]+1;q.append(w)
  out.append(ds)
 return out
