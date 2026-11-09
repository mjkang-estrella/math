import pathlib,resource,json,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
def prefixes(k,t,N):
 a=[[0]*(2*N) for _ in range(2*N)]
 for i in range(2*N):
  for j in range(i+1,2*N):
   a[i][j]=t if i==0 else (a[i-1][j]+a[i-1][j-1]+k*(-1)**i if j==i+1 else a[i-1][j]+a[i][j-1]+a[i-1][j-1]);a[j][i]=-a[i][j]
 prev=1;ps=[]
 for z in range(0,2*N,2):
  p=a[z][z+1];ps.append(p)
  if not p:return ps,'zero pivot'
  for i in range(z+2,2*N):
   for j in range(i+1,2*N):
    v=a[i][j]*p-a[z][i]*a[z+1][j]+a[z][j]*a[z+1][i]
    assert v%prev==0
    a[i][j]=v//prev
  prev=p
 return ps,'complete'
for k in range(-12,25):
 for t in [1,2,3]:
  ps,status=prefixes(k,t,48);o=1;fail=None
  for n,p in enumerate(ps,1):
   d=t*o
   if not d:break
   if p%d:fail={'n':n,'pf':p,'previous_o':o,'remainder':p%d};break
   o=p//d
  print(json.dumps({'k':k,'t':t,'prefixes':len(ps),'status':status,'failure':fail,'last_o':o}),flush=True)
