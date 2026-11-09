from pathlib import Path
import resource,itertools,json,random,time
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(75,75))
O=Path(__file__).resolve().parent;start=time.monotonic()
def children(w):
 for l in range(1,len(w)//2+1):
  for i in range(len(w)-2*l+1):
   if w[i:i+l]==w[i+l:i+2*l]:yield w[:i]+w[i+l:]
D={'':0};SF={'':True};rows=[]
for n in range(1,11):
 maximum=0;mw=None;joinmax=0;jw=None
 for t in itertools.product('012',repeat=n):
  w=''.join(t);ch=list(children(w));d=1+min(D[v] for v in ch) if ch else 0;D[w]=d;SF[w]=not ch
  if d>maximum:maximum=d;mw=w
  if d>joinmax:
   splits=[i for i in range(1,n) if SF[w[:i]] and SF[w[i:]]]
   if splits:joinmax=d;jw=[w,splits[0]]
 row=dict(n=n,d3=maximum,witness=mw,two_squarefree_join_max=joinmax,join_witness=jw);rows.append(row);print('word',row,flush=True)
(O/'word-diagnostics.json').write_text(json.dumps(rows,indent=2)+'\n')
# A fixed resolving set fails to be double precisely at nonzero constant-offset pairs.
rng=random.Random(2101);out=[]
for n,size,trials in [(3,3,20),(4,6,30),(5,4,500),(6,8,300),(7,6,1200)]:
 N=2**(n-1);d=[[min((u^v).bit_count(),n-(u^v).bit_count()) for v in range(N)] for u in range(N)]
 count=0;badcount=0;noaugment=0;worst=None
 for trial in range(trials):
  S=[0]+rng.sample(range(1,N),size-1);vectors=[tuple(d[u][s] for s in S) for u in range(N)]
  if len(set(vectors))<N:continue
  count+=1;groups={};bad=[]
  for u,v in enumerate(vectors):
   sig=tuple(x-v[0] for x in v)
   for z in groups.get(sig,[]):bad.append((z,u,d[z][0]-d[u][0]))
   groups.setdefault(sig,[]).append(u)
  if not bad:continue
  badcount+=1
  good=[t for t in range(N) if all(d[u][t]-d[v][t]!=c for u,v,c in bad)]
  if not good:noaugment+=1
  if worst is None or len(bad)>len(worst['bad_pairs']):worst=dict(S=S,bad_pairs=bad,augmenting_vertices=good)
 row=dict(n=n,tested_size=size,trials=trials,resolving=count,not_double=badcount,no_single_augmentation=noaugment,worst=worst);out.append(row);print('cube',row,flush=True)
(O/'cube-diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print('seconds',time.monotonic()-start)
