import resource,os,itertools,json,collections
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(150,150));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
P=Path(__file__).resolve().parent

def ups(adj):
 n=len(adj)
 for k in range(1,n+1):
  for c in itertools.combinations(range(n),k):
   u=(1<<n)-1
   for v in c:u &= adj[v]
   if u.bit_count()<=k:return k

def solve(adj,k):
 n=len(adj);full=(1<<n)-1;cs=list(itertools.combinations_with_replacement(range(n),k));occ=[sum(1<<v for v in set(c)) for c in cs];us=[];states=[];idx={}
 for ci,c in enumerate(cs):
  u=full
  for v in c:u &= adj[v]
  u &=~occ[ci];us.append(u);b=u
  while b:idx[(ci,b)]=len(states);states.append((ci,b));b=(b-1)&u
  for v in range(n):
   if not(occ[ci]>>v&1) and not(u>>v&1):idx[(ci,1<<v)]=len(states);states.append((ci,1<<v))
 ciidx={c:i for i,c in enumerate(cs)};moves=[]
 for c in cs:
  ms=set()
  for t in itertools.product(*[[w for w in range(n) if w==v or adj[v]>>w&1] for v in c]):ms.add(ciidx[tuple(sorted(t))])
  moves.append(sorted(ms))
 step=[]
 for b in range(1<<n):
  u=b
  for v in range(n):
   if b>>v&1:u |=adj[v]
  step.append(u)
 # Hyperedge reachability: a cops action wins once every observation successor wins.
 rev=[[] for _ in states];remain=[];owner=[];win=[False]*len(states);q=collections.deque()
 for si,(ci,b) in enumerate(states):
  for cj in moves[ci]:
   alive=b & ~occ[cj]
   if not alive:
    if not win[si]:win[si]=True;q.append(si)
    continue
   post=step[alive]&~occ[cj];ob=[];invis=post&us[cj]
   if invis:ob.append(idx[(cj,invis)])
   for v in range(n):
    if post>>v&1 and not(us[cj]>>v&1):ob.append(idx[(cj,1<<v)])
   aid=len(remain);remain.append(len(ob));owner.append(si)
   for t in ob:rev[t].append(aid)
   if not ob and not win[si]:win[si]=True;q.append(si)
   if len(remain)>2000000:raise RuntimeError('action cap')
 while q:
  t=q.popleft()
  for aid in rev[t]:
   remain[aid]-=1
   if not remain[aid] and not win[owner[aid]]:win[owner[aid]]=True;q.append(owner[aid])
 for ci,c in enumerate(cs):
  bs=[]
  if us[ci]:bs.append(us[ci])
  bs += [1<<v for v in range(n) if not(occ[ci]>>v&1) and not(us[ci]>>v&1)]
  if all(win[idx[(ci,b)]] for b in bs):return True,len(states),len(remain),c
 return False,len(states),len(remain),None

def connected(a):
 seen=1
 while True:
  t=seen
  for v in range(len(a)):
   if seen>>v&1:t |=a[v]
  if t==seen:return seen==(1<<len(a))-1
  seen=t
factors=[]
for n in range(1,6):
 edges=list(itertools.combinations(range(n),2));seen=set()
 for b in range(1<<len(edges)):
  a=[0]*n
  for i,(v,w) in enumerate(edges):
   if b>>i&1:a[v]|=1<<w;a[w]|=1<<v
  if not connected(a):continue
  canon=min(tuple(sum(1<<j for j in range(n) if a[p[i]]>>p[j]&1) for i in range(n)) for p in itertools.permutations(range(n)))
  if canon in seen:continue
  seen.add(canon);u=ups(a);ch=next(k for k in range(1,u+2) if solve(a,k)[0]);factors.append((a,u,ch))
  print('factor',a,'ups',u,'cH',ch,flush=True)
rows=[]
for (a,u,c),(b,v,d) in itertools.combinations_with_replacement(factors,2):
 bound=min(u,c)+min(v,d)
 if bound>=u+v:continue # already source Theorem10
 n=len(a);m=len(b);adj=[x|(((1<<m)-1)<<n) for x in a]+[(x<<n)|((1<<n)-1) for x in b]
 r=solve(adj,bound);rows.append({'a':a,'b':b,'bound':bound,'winning':r[0],'states':r[1],'actions':r[2],'start':r[3]});print('join',rows[-1],flush=True)
(P/'hyperopic-diagnostic.json').write_text(json.dumps({'factors':factors,'joins':rows},indent=2)+'\n')
