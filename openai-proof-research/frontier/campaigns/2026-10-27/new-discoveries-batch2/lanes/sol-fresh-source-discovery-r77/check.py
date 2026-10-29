import itertools,collections,json,pathlib
D=pathlib.Path(__file__).resolve().parent
class Flow:
 def __init__(self,n):self.g=[[] for _ in range(n)]
 def edge(self,u,v,c):
  a=[v,c,None];b=[u,0,a];a[2]=b;self.g[u].append(a);self.g[v].append(b)
 def run(self,s,t):
  ans=0
  while True:
   level=[-1]*len(self.g);level[s]=0;q=collections.deque([s])
   while q:
    u=q.popleft()
    for v,c,_ in self.g[u]:
     if c and level[v]<0:level[v]=level[u]+1;q.append(v)
   if level[t]<0:break
   at=[0]*len(self.g)
   def dfs(u,f):
    if u==t:return f
    while at[u]<len(self.g[u]):
     a=self.g[u][at[u]];v,c,b=a
     if c and level[v]==level[u]+1:
      z=dfs(v,min(c,f))
      if z:a[1]-=z;b[1]+=z;return z
     at[u]+=1
    return 0
   while z:=dfs(s,10**100):ans+=z
  return ans

def coupling(left,right,edges):
 a=sum(left);b=sum(right);s=len(left)+len(right);t=s+1;f=Flow(t+1)
 for i,w in enumerate(left):f.edge(s,i,w*b)
 for j,w in enumerate(right):f.edge(len(left)+j,t,w*a)
 for i,j in edges:f.edge(i,len(left)+j,a*b)
 got=f.run(s,t)
 return got==a*b,got,a*b

def refines(p,q):
 return all(p[i]==p[j] or q[i]!=q[j] for i in range(len(p)) for j in range(i))

def fibers(n):
 out=collections.defaultdict(collections.Counter)
 for f in itertools.product(*(range(i+1) for i in range(n))):
  seen={};p=[];B=0
  for i,x in enumerate(f):
   if x not in seen:seen[x]=len(seen);B|=1<<i
   p.append(seen[x])
  out[B][tuple(p)]+=1
 return out
results=[];witness=None;typefail=[]
for n in range(2,7):
 F=fibers(n);good=set();bad=[]
 for B in F:
  for v in range(1,n):
   if B>>v&1:continue
   C=B|1<<v;P=list(F[B]);Q=list(F[C]);edges=[(i,j) for i,p in enumerate(P) for j,q in enumerate(Q) if refines(p,q)]
   ok,got,need=coupling(list(F[B].values()),list(F[C].values()),edges)
   if ok:good.add((B,C))
   else:
    bad.append((B,C))
    if witness is None:
     witness={'n':n,'B':[i+1 for i in range(n) if B>>i&1],'C':[i+1 for i in range(n) if C>>i&1], 'left':list(zip(P,F[B].values())),'right':list(zip(Q,F[C].values())),'edges':edges,'flow':got,'required':need}
 for ell in range(2,31):
  for k in range(1,n):
   L=[B for B in F if B.bit_count()==k];R=[B for B in F if B.bit_count()==k+1]
   edges=[(i,j) for i,B in enumerate(L) for j,C in enumerate(R) if (B,C) in good]
   ok,got,need=coupling([sum(F[B].values())**ell for B in L],[sum(F[C].values())**ell for C in R],edges)
   if not ok:typefail.append({'n':n,'ell':ell,'k':k,'flow':got,'required':need})
 results.append({'n':n,'fiber_pairs_pass':len(good),'fiber_pairs_fail':len(bad)})
print(json.dumps({'results':results,'first_bad_fiber':witness,'type_checks':sum(29*(n-1) for n in range(2,7)),'type_failures_count':len(typefail),'first_type_failures':typefail[:8]},indent=2))
