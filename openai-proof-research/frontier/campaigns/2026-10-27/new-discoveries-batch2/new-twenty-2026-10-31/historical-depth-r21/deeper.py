from pathlib import Path
import resource,json,time,itertools,random
from functools import lru_cache
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(55,55))
O=Path(__file__).resolve().parent;start=time.monotonic()
def canonical(w):
 d={};return ''.join(d.setdefault(c,str(len(d))) for c in w)
def children(w):
 return {w[:i]+w[i+l:] for l in range(1,len(w)//2+1) for i in range(len(w)-2*l+1) if w[i:i+l]==w[i+l:i+2*l]}
@lru_cache(maxsize=150000)
def dist(w):
 c=children(w);return 1+min(dist(canonical(v)) for v in c) if c else 0
sf=[''];all_sf=[]
for n in range(1,11):
 sf=[w+c for w in sf for c in '012' if not children(w+c)];all_sf+=sf
best={};tested=0
for a in all_sf:
 for b in all_sf:
  if len(a)+len(b)>18:continue
  w=a+b;d=dist(canonical(w));tested+=1;n=len(w)
  if n not in best or best[n]['distance']<d:
   best[n]=dict(distance=d,A=a,B=b)
  if time.monotonic()-start>30:break
 else:continue
 break
print(json.dumps(dict(kind='squarefree_join',tested=tested,best=best,cache=str(dist.cache_info()),seconds=time.monotonic()-start)),flush=True)
(O/'deeper-word.json').write_text(json.dumps(dict(tested=tested,best=best,range='ternary squarefree factors each length <=10; total <=18',exhaustion_completed=time.monotonic()-start<=30),indent=2)+'\n')
# Exact all translation-normalized four-vertex bases at n=5; sample n=7.
rng=random.Random(2102);out=[]
for n,size,trials in [(5,4,0),(7,6,5000)]:
 N=2**(n-1);d=[[min((u^v).bit_count(),n-(u^v).bit_count()) for v in range(N)] for u in range(N)];neighbors=[1<<i for i in range(n-1)]+[N-1]
 sets=([0]+list(t) for t in itertools.combinations(range(1,N),3)) if n==5 else ([0]+rng.sample(range(1,N),size-1) for _ in range(trials))
 row=dict(n=n,resolving=0,not_double=0,no_neighbor_augmentation=0,no_augmentation=0,max_offset=0,max_bad_pairs=0,obstruction=None)
 for S in sets:
  v=[tuple(d[u][s] for s in S) for u in range(N)]
  if len(set(v))<N:continue
  row['resolving']+=1;groups={};bad=[]
  for u,vv in enumerate(v):
   sig=tuple(x-vv[0] for x in vv)
   for z in groups.get(sig,[]):bad.append((z,u,d[z][0]-d[u][0]))
   groups.setdefault(sig,[]).append(u)
  if not bad:continue
  row['not_double']+=1;row['max_offset']=max(row['max_offset'],max(abs(c) for u,v,c in bad));row['max_bad_pairs']=max(row['max_bad_pairs'],len(bad))
  good=[t for t in range(N) if all(d[u][t]-d[v][t]!=c for u,v,c in bad)]
  if not good:row['no_augmentation']+=1
  if not set(good)&set(neighbors):row['no_neighbor_augmentation']+=1;row['obstruction']=dict(S=S,bad=bad,good=good)
 out.append(row);print(json.dumps(row),flush=True)
(O/'deeper-cube.json').write_text(json.dumps(out,indent=2)+'\n')
