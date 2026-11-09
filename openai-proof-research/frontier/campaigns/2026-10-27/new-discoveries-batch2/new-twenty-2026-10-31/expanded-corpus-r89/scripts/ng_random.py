from small_graphs import posvalid,chrom
import random,json,time
r=random.Random(8989);start=time.monotonic()
for n in range(7,13):
 worst={k:[0,None] for k in ['gp','mp']};count=0
 for j in range(400):
  prob=[.15,.25,.4,.5,.65,.8][j%6];a=[0]*n
  for u in range(n):
   for v in range(u):
    if r.random()<prob:a[u]|=1<<v;a[v]|=1<<u
  b=[((1<<n)-1)^(1<<v)^a[v] for v in range(n)]
  for k in worst:
   z=chrom(n,posvalid(a,k=='mp'))+chrom(n,posvalid(b,k=='mp'))
   if z>worst[k][0]:worst[k]=[z,a]
   if z>n+1:print(json.dumps(dict(counterexample=True,n=n,kind=k,sum=z,adj=a)),flush=True);raise SystemExit
  count+=1
  if time.monotonic()-start>110:break
 print(json.dumps(dict(n=n,graphs=count,worst=worst,seed=8989)),flush=True)
 if time.monotonic()-start>110:break
