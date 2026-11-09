import itertools,pathlib,json,os,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(2,7):
 bc=[0]*n;mc=[0]*n;b={};m={(1,j):j for j in range(1,n+1)};Bcells=[(i,j) for i in range(1,n) for j in range(i,n)];Mcells=[(i,j) for i in range(2,n+1) for j in range(i,n+1)]
 def B(z):
  if z==len(Bcells):
   for k in range(n):
    if all(v==n for (i,j),v in b.items() if j<=n-1-k):bc[k]+=1
   return
  i,j=Bcells[z];upper=min(n,b.get((i,j-1),n),b.get((i-1,j),n))
  for v in range(n-i,upper+1):b[i,j]=v;B(z+1)
  b.pop((i,j),None)
 def M(z):
  if z==len(Mcells):
   for k in range(n):
    if all(v==j-i+1 for (i,j),v in m.items() if j<=n-k):mc[k]+=1
   return
  i,j=Mcells[z];lower=max(m[i-1,j-1],m.get((i,j-1),0)+1);upper=m[i-1,j]
  for v in range(lower,upper+1):m[i,j]=v;M(z+1)
  m.pop((i,j),None)
 B(0);M(0);row={'id':379545,'n':n,'restricted_TSPP_counts':bc,'restricted_monotone_triangle_counts':mc,'constraints':'Source Definition3.2 m=0 and M1-M4, column constraints j<=n-1-k and j<=n-k'};out.append(row);print(json.dumps(row),flush=True);(D/'outputs/triangles-search.json').write_text(json.dumps(out,indent=2))
