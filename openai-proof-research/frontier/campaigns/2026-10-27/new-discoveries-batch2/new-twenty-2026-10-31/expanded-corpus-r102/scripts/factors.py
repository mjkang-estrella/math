import itertools,json,time,random
props=[(1,2,3),(0,1,5),(1,1,4),(2,2,2)] # numerator /6

def solve(n,edges,ep,pin):
 deg=[sum(v in e for e in edges) for v in range(n)];allowed=[]
 for v in range(n):
  aa=[]
  for a in range(deg[v]+1):
   for b in range(deg[v]-a+1):
    dd=(a,b,deg[v]-a-b)
    if sum(d%2 for d in dd)>1:continue
    if pin and deg[v]%2 and dd[0]%2!=1:continue
    if all(abs(6*dd[i]-ep[i]*deg[v])<12 for i in range(3)):aa.append(dd)
  allowed.append(aa)
 ds=[[0]*3 for _ in range(n)];left=deg[:]
 def dfs(k):
  if k==len(edges):return True
  a,b=edges[k];left[a]-=1;left[b]-=1
  for c in range(3):
   ds[a][c]+=1;ds[b][c]+=1
   ok=all(any(all(ds[v][i]<=x[i]<=ds[v][i]+left[v] for i in range(3)) for x in allowed[v]) for v in [a,b])
   if ok and dfs(k+1):return True
   ds[a][c]-=1;ds[b][c]-=1
  left[a]+=1;left[b]+=1
  return False
 return dfs(0)
def oddconn(n,es,ep):
 if ep[0]==0:return False
 k=(6+ep[0]-1)//ep[0]
 return all(not(cut%2) or cut>=k for mask in range(1,1<<(n-1)) for cut in [sum(((mask>>a)&1)!=((mask>>b)&1) for a,b in es)])
for n in range(2,6):
 start=time.monotonic();es=list(itertools.combinations(range(n),2));tests=0;pin_tests=0;fails=[]
 for mask in range(1<<len(es)):
  edges=[e for i,e in enumerate(es) if mask>>i&1]
  for ep in props:
   pin=oddconn(n,edges,ep);tests+=1;pin_tests+=pin
   if not solve(n,edges,ep,pin):fails.append({'edges':edges,'proportions_numerator':ep,'pin':pin})
 print(json.dumps({'n':n,'graphs':1<<len(es),'proportions_denominator':6,'proportions_numerators':props,'tests':tests,'pinned_tests':pin_tests,'fails':fails,'seconds':time.monotonic()-start}),flush=True)
