import os,resource,time,json,pathlib,math
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));L=pathlib.Path(__file__).resolve().parents[1];st=time.monotonic()
def root(g,v,p):return '('+''.join(sorted(root(g,w,v) for w in g[v] if w!=p))+')'
def canon(g):return min(root(g,v,-1) for v in range(len(g)))
def en(g):
 n=len(g);a=[[0.0]*n for _ in g]
 for i in range(n):
  for j in g[i]:a[i][j]=1/math.sqrt(len(g[i])*len(g[j]))
 for it in range(40):
  mx=0
  for p in range(n):
   for q in range(p+1,n):
    v=a[p][q];mx=max(mx,abs(v))
    if abs(v)<1e-13:continue
    tau=(a[q][q]-a[p][p])/(2*v);t=math.copysign(1,tau)/(abs(tau)+math.sqrt(1+tau*tau));c=1/math.sqrt(1+t*t);s=t*c
    a[p][p]-=t*v;a[q][q]+=t*v;a[p][q]=a[q][p]=0
    for k in range(n):
     if k!=p and k!=q:
      x,y=a[k][p],a[k][q];a[k][p]=a[p][k]=c*x-s*y;a[k][q]=a[q][k]=s*x+c*y
  if mx<1e-11:break
 return sum(abs(a[i][i]) for i in range(n))
def sun(n):
 g=[[] for _ in range(n)]
 def e(a,b):g[a].append(b);g[b].append(a)
 if n%2:
  for i in range((n-1)//2):e(0,1+2*i);e(1+2*i,2+2*i)
 else:
  e(0,1);z=(n-2)//2
  for i in range(z):e(0 if i<(z+1)//2 else 1,2+2*i);e(2+2*i,3+2*i)
 return g
prev=[[[1],[0]]];out=[]
for n in range(3,16):
 curr={}
 for g in prev:
  for v in range(n-1):
   h=[x[:] for x in g]+[[v]];h[v].append(n-1);curr.setdefault(canon(h),h)
 bound=en(sun(n));best=-1;key=None;count=0
 for s,g in curr.items():
  e=en(g);count+=1
  if e>best:best,key=e,s
  if time.monotonic()-st>100:break
 r={'n':n,'generated_nonisomorphic_trees':len(curr),'tested':count,'complete':count==len(curr),'sun_energy':bound,'maximum_numeric_energy':best,'excess':best-bound,'maximizer_canonical':key};out.append(r);print(json.dumps(r),flush=True)
 if best>bound+1e-8 or time.monotonic()-st>100:break
 prev=list(curr.values())
(L/'randic-results.json').write_text(json.dumps({'diagnostic_only':True,'elapsed':time.monotonic()-st,'rows':out},indent=2))
