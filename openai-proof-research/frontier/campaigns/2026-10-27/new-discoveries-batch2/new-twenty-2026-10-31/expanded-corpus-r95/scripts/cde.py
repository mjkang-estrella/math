import itertools,json,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
def cde(lam):
 states=[x for x in itertools.product(*(range(v+1) for v in lam)) if all(x[i]>x[i+1] or x[i]==x[i+1]==0 for i in range(len(x)-1))];states.sort(key=sum);zero=(0,)*len(lam);f={zero:1};prev={};degree={}
 for x in states:
  ps=[]
  for i,v in enumerate(x):
   if v:
    y=list(x);y[i]-=1;y=tuple(y)
    if i==len(x)-1 or y[i]>y[i+1] or y[i]==y[i+1]==0:ps.append(y)
  prev[x]=ps;degree[x]=len(ps)
  if x!=zero:f[x]=sum(f[y] for y in ps)
 b={x:0 for x in states};b[lam]=1
 for x in states[::-1]:
  for y in prev[x]:b[y]+=b[x]
 lhs=sum(degree.values())*(sum(lam)+1)*f[lam];rhs=len(states)*sum(degree[x]*f[x]*b[x] for x in states)
 return lhs==rhs,len(states),sum(degree.values()),f[lam]
for size in range(3,101):
 found=[];tested=0
 for a in range(size, size//2,-1):
  b=size-a
  if b==0:continue
  lam=(a,b);ok,num,edges,paths=cde(lam);tested+=1
  if ok:found.append(lam)
 print(json.dumps({'size':size,'two_row_tested':tested,'CDE':found}),flush=True)
