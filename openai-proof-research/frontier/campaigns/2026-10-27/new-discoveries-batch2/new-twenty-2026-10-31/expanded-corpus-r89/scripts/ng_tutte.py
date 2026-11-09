import itertools,random,json,time,sys
from small_graphs import posvalid,chrom
seed=int(sys.argv[1]);r=random.Random(seed);start=time.monotonic();count=0;worst={};nontrivial=0
while time.monotonic()-start<105 and count<600:
 s=r.choice([1,2,3]);parts=[r.choice([1,1,3,3,5]) for _ in range(r.randint(s+2,s+4))];n=s+sum(parts)
 if n<11 or n>15:continue
 a=[0]*n
 def edge(u,v):a[u]|=1<<v;a[v]|=1<<u
 offset=s
 for k in parts:
  vs=list(range(offset,offset+k));offset+=k
  for u,v in itertools.combinations(vs,2):
   if r.random()<.9:edge(u,v)
  for v in vs:
   # force each vertex into at least one barrier neighbourhood, keep complement nontrivial
   nbr=[u for u in range(s) if r.random()<.55]
   if not nbr:nbr=[r.randrange(s)]
   for u in nbr:edge(u,v)
 for u,v in itertools.combinations(range(s),2):
  if r.random()<.5:edge(u,v)
 b=[((1<<n)-1)^(1<<v)^a[v] for v in range(n)]
 for k in ['gp','mp']:
  z1=chrom(n,posvalid(a,k=='mp'));z2=chrom(n,posvalid(b,k=='mp'));z=z1+z2
  key=k+str(n)
  if key not in worst or z>worst[key]['sum']:
   worst[key]=dict(sum=z,chis=[z1,z2],adj=a,s=s,parts=parts)
  if z>n+1:
   print(json.dumps(dict(counterexample=True,n=n,kind=k,**worst[key])),flush=True);raise SystemExit
 count+=1
 if count%50==0:print(json.dumps(dict(progress=count,elapsed=time.monotonic()-start)),flush=True)
print(json.dumps(dict(seed=seed,graphs=count,counterexample=False,worst=worst,elapsed=time.monotonic()-start)),flush=True)
