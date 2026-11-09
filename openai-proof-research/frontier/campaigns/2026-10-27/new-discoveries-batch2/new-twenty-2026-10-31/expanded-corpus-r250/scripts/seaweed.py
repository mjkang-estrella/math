import itertools,collections,json,random,sys,time

def comp(n):
 for mask in range(1<<(n-1)):
  cuts=[0]+[i+1 for i in range(n-1) if mask>>i&1]+[n]
  yield tuple(cuts[i+1]-cuts[i] for i in range(len(cuts)-1))
def check(a,b):
 n=sum(a);adj=[[] for _ in range(n)];blocks=[]
 for top,c in [(True,a),(False,b)]:
  s=0
  for k in c:
   blocks.append((top,s,k))
   for i in range(k//2):
    u,v=s+i,s+k-1-i
    if top:u,v=v,u
    adj[u].append((v,1));adj[v].append((u,-1))
   s+=k
 if sum(len(x) for x in adj)!=2*n-2:return None
 h=[None]*n;h[0]=0;stack=[0]
 while stack:
  u=stack.pop()
  for v,w in adj[u]:
   if h[v] is None:h[v]=h[u]+w;stack.append(v)
 if None in h:return None
 for top,s,k in blocks:
  ds=collections.Counter({0:k//2})
  for i in range(s,s+k):
   for j in range(s,i):ds[(h[j]-h[i]) if top else (h[i]-h[j])]+=1
  if not ds:continue
  lo,hi=min(ds),max(ds);seq=[ds[i] for i in range(lo,hi+1)]
  if any(ds[i]>ds[i+1] for i in range(lo,0)) or any(ds[i]<ds[i+1] for i in range(1,hi)):
   return dict(a=a,b=b,h=h,top=top,start=s,size=k,lo=lo,counts=seq)
 return False
random.seed(250);start=time.monotonic()
if sys.argv[1]=='exhaustive':
 for n in range(2,int(sys.argv[2])+1):
  cs=list(comp(n));fro=0
  for a in cs:
   for b in cs:
    r=check(a,b)
    if r is not None:fro+=1
    if r:print(json.dumps({'counterexample':r}),flush=True);sys.exit()
  print(json.dumps(dict(n=n,pairs=len(cs)**2,frobenius=fro,wall=time.monotonic()-start)),flush=True)
else:
 tested=0;fro=0
 for n in [20,30,50,80,120,200]:
  for trial in range(2000):
   def rc():
    cuts=sorted(random.sample(range(1,n),random.randrange(1,min(15,n-1))))
    return tuple(v-u for u,v in zip([0]+cuts,cuts+[n]))
   a,b=rc(),rc();r=check(a,b);tested+=1
   if r is not None:fro+=1
   if r:print(json.dumps({'counterexample':r}),flush=True);sys.exit()
  print(json.dumps(dict(n=n,tested=tested,frobenius=fro,wall=time.monotonic()-start)),flush=True)
