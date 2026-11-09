import random,itertools,json,sys,time
random.seed(144)
def connected(a):
 seen=1;prev=0
 while seen!=prev:
  prev=seen
  for i in range(len(a)):
   if seen>>i&1:seen|=a[i]
 return seen==(1<<len(a))-1
def colorings(conf,k):
 n=len(conf);c=[0]*n
 def go(i,m):
  if i==n:yield tuple(c);return
  for x in range(min(m+1,k)):
   if any(c[j]==x and conf[i]>>j&1 for j in range(i)):continue
   c[i]=x;yield from go(i+1,max(m,x+1))
 yield from go(0,0)
def cuts(a):
 n=len(a);out=[]
 for u in range(n):
  for v in range(u+1,n):
   adj=a[u]>>v&1;cs=[]
   for s in range(1<<n):
    if s&(1<<u|1<<v):continue
    seen=1<<u;prev=-1
    while seen!=prev:
     prev=seen
     for i in range(n):
      if seen>>i&1:
       neigh=a[i]&~s
       if i==u:neigh&=~(1<<v)
       if i==v:neigh&=~(1<<u)
       seen|=neigh
    if not seen>>v&1:cs.append(tuple(i for i in range(n) if s>>i&1))
   out.append((u,v,adj,cs))
 return out
def rvd(a,limit):
 n=len(a);conf=[sum(1<<j for j in range(n) if j!=i and (a[i]&a[j]).bit_count()>=2) for i in range(n)]
 cc=None;tries=0
 for k in range(1,limit+1):
  for c in colorings(conf,k):
   if cc is None:cc=cuts(a)
   tries+=1;valid=True
   for u,v,adj,cs in cc:
    if not any(len({c[i] for i in s})==len(s) and (not adj or c[u] not in {c[i] for i in s} or c[v] not in {c[i] for i in s}) for s in cs):
     valid=False;break
   if valid:return k,c,tries
 return limit+1,None,tries
n=int(sys.argv[1]);count=int(sys.argv[2]);passed=0;eligible=0
for it in range(count):
 p=random.choice([.2,.3,.4,.5,.6,.7,.8]);a=[0]*n;allm=(1<<n)-1
 for u in range(n):
  for v in range(u+1,n):
   if random.random()<p:a[u]|=1<<v;a[v]|=1<<u
 b=[allm^(1<<i)^a[i] for i in range(n)]
 if not connected(a) or not connected(b):continue
 eligible+=1
 x,c,t=rvd(a,n-2)
 if x==n-1:passed+=1;continue
 y,d,s=rvd(b,n-x-1)
 if y<n-x:
  print(json.dumps(dict(COUNTEREXAMPLE=True,a=a,x=x,c=c,y=y,d=d)),flush=True);break
 passed+=1
 if eligible%100==0:print(json.dumps(dict(n=n,it=it,eligible=eligible,passed=passed)),flush=True)
else:print(json.dumps(dict(n=n,draws=count,eligible=eligible,passed=passed,completed=True)),flush=True)
