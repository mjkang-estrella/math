from pathlib import Path
import os,resource,time,json,itertools,random,functools
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(180,180))
p=Path(__file__).resolve().parent;start=time.monotonic();out={}
# Exact integer coefficient model; half-integral e uses q=square.
def poly(q,qe,d,i):
 a=[1]
 for b in [qe*q**s for s in range(d-i)]+[-q**s for s in range(i)]:
  a=[a[0]]+[a[k]+b*a[k-1] for k in range(1,len(a))]+[b*a[-1]]
 return a
fails=[];count=0;locfails=[]
for q,ee in [(q,e) for q in [2,3,4,5,7,8,9,16] for e in [0,2,4]]+[(q,e) for q in [4,9,16] for e in [1,3]]:
 qe=q**(ee//2) if ee%2==0 else int(q**0.5)**ee
 for d in range(2,41):
  rows=[poly(q,qe,d,i) for i in range(d+1)]
  for j in range(1,d+1):
   count+=1;a=[abs(r[j]) for r in rows];m=min(a);mins=[i for i,v in enumerate(a) if v==m]; valley=any(all(a[k]>=a[k+1] for k in range(i)) and all(a[k]<=a[k+1] for k in range(i,d)) for i in mins)
   excluded=(q==2 and ee==2) or(q==2 and ee==4 and j==d-4 and 8<=d<=12)
   if not valley and not excluded:fails.append([q,ee,d,j,a])
   i1=(2*d+ee+2)//4
   allowed=[i1] if ee in [0,1,3] else [i1-1,i1,i1+1]
   if (q,ee,j,d) in [(2,2,3,4),(2,4,3,7)]:allowed=[i1-2]
   if valley and not any(i in allowed for i in mins):locfails.append([q,ee,d,j,mins])
out['dual_polar']={'columns':count,'d_range':[2,40],'new_valley_failures':fails,'minimum_location_failures':locfails,'warning':'Exact integer diagnostics, coefficient/eigenvalue bridge not kernel-certified; ties interpreted existentially.'}
# Swap sets: exact exhaustive subset search per graph; each side size, not union size.
def analyze(adj):
 n=len(adj);allv=(1<<n)-1;closed=[a|(1<<i) for i,a in enumerate(adj)];dom=[0]*(1<<n);ind=[False]*(1<<n);ind[0]=True;alpha=0;ds=[[] for _ in range(n+1)]
 for s in range(1,1<<n):
  bit=s&-s;i=bit.bit_length()-1;t=s^bit;dom[s]=dom[t]|closed[i];ind[s]=ind[t] and not(adj[i]&t)
  if ind[s]:alpha=max(alpha,s.bit_count())
  if dom[s]==allv and s.bit_count()<=n//2:ds[s.bit_count()].append(s)
 def match(a,b):
  if not a:return True
  bit=a&-a;i=bit.bit_length()-1;opts=adj[i]&b
  while opts:
   t=opts&-opts;opts-=t
   if match(a^bit,b^t):return True
  return False
 for k in range(1,n//2+1):
  for a in ds[k]:
   for b in ds[k]:
    if b>a and not a&b and match(a,b):return alpha,k,[a,b]
 return alpha,None,None
rng=random.Random(170336964);stats={};witness=[]
for n in [8,9,10,11,12]:
 for density in [0.15,0.25,0.4,0.6]:
  key=f'{n}:{density}';total=0;has=0
  for trial in range(60):
   a=[0]*n
   for i in range(n):
    for j in range(i):
     if rng.random()<density:a[i]|=1<<j;a[j]|=1<<i
   # connected check
   seen=1
   while True:
    nxt=seen
    for i in range(n):
     if seen>>i&1:nxt|=a[i]
    if nxt==seen:break
    seen=nxt
   if seen!=(1<<n)-1:continue
   total+=1;alpha,k,pair=analyze(a);has+=k is not None
   if k and k>alpha:witness.append({'adj':a,'alpha':alpha,'swap':k,'pair':pair})
  stats[key]={'connected':total,'has_swap':has}
out['swap']={'seed':170336964,'stats':stats,'counterexamples':witness,'warning':'All subset pairs/matchings exact per sampled graph, graphs not exhaustive; no Lean certificate.'}
out['resources']={'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit_s':180,'address_space_bytes':3*1024**3,'elapsed_s':time.monotonic()-start,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(p/'diagnostics.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:6000])
