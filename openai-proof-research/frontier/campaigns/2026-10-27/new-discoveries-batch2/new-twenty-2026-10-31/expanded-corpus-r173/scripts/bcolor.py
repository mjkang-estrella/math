import pathlib,itertools,json,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
def graphs(n):
 es=list(itertools.combinations(range(n),2))
 for mask in range(1<<len(es)):
  a=[0]*n
  for j,(u,v) in enumerate(es):
   if mask>>j&1:a[u]|=1<<v;a[v]|=1<<u
  yield a
def dist(a):
 n=len(a);d=[[0 if i==j else (1 if a[i]>>j&1 else 100) for j in range(n)] for i in range(n)]
 for k in range(n):
  for i in range(n):
   for j in range(n):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
 return d
def bc(a):
 n=len(a);order=sorted(range(n),key=lambda i:-a[i].bit_count());c=[-1]*n;best=0;nodes=0
 def rec(p,used):
  nonlocal best,nodes
  nodes+=1
  if nodes>3000000:raise TimeoutError
  if used+n-p<=best:return
  if p==n:
   dom=0
   for v in range(n):
    seen=1<<c[v]
    for u in range(n):
     if a[v]>>u&1:seen|=1<<c[u]
    if seen==(1<<used)-1:dom|=1<<c[v]
   if dom==(1<<used)-1:best=max(best,used)
   return
  v=order[p];ban={c[u] for u in range(n) if a[v]>>u&1 and c[u]>=0}
  for x in range(used+1):
   if x in ban:continue
   c[v]=x;rec(p+1,max(used,x+1));c[v]=-1
 rec(0,0);return best,nodes
rows=[];tested=0;skipped=0
pairs=[(2,2),(2,3),(3,3),(2,4)] if len(sys.argv)==1 else [(3,4)]
for n,m in pairs:
 for gi,g in enumerate(graphs(n)):
  dg=dist(g)
  for hi,h in enumerate(graphs(m)):
   dh=dist(h)
   for k in [2,3]:
    a=[0]*(n*m);b=a.copy()
    for u in range(n*m):
     i,j=divmod(u,m)
     for v in range(u):
      r,s=divmod(v,m)
      if dg[i][r]+dh[j][s]<=k:a[u]|=1<<v;a[v]|=1<<u
      if (i==r and dh[j][s]<=k) or (j==s and dg[i][r]<=k):b[u]|=1<<v;b[v]|=1<<u
    try:x,nx=bc(a);y,ny=bc(b)
    except TimeoutError:skipped+=1;continue
    tested+=1
    if x<y:rows.append({'n':n,'m':m,'gmask':gi,'hmask':hi,'k':k,'left':x,'right':y,'g':g,'h':h});print('FOUND',rows[-1],flush=True)
 print(n,m,'tested',tested,'node_cap_skipped',skipped,flush=True)
r={'pairs':pairs,'k':[2,3],'tested':tested,'node_cap_skipped':skipped,'counterexamples':rows,'method':'all labelled factors; exhaustive canonical proper set partitions; every color has a dominating vertex; per-invariant node cap3000000'}
(D/('outputs/bcolor'+('34' if len(sys.argv)>1 else '')+'.json')).write_text(json.dumps(r,indent=2));print(r)
