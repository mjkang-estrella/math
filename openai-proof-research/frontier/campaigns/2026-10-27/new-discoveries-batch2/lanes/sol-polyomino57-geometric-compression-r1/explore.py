import resource,signal,os,json,itertools,collections,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(100,105));signal.alarm(115)
L=os.path.dirname(__file__)
H={(2,2),(2,-2),(-2,2),(-2,-2)}
def centers(P,r=5):
 u=[x+y for x,y in P];v=[x-y for x,y in P]
 return [((a+b)//2,(a-b)//2) for a in range(max(u)-r,min(u)+r+1) for b in range(max(v)-r,min(v)+r+1) if (a-b)%2==0]
def good(P):
 return [c for c in centers(P) if all((x-c[0],y-c[1]) not in H for x,y in P)]
def connected(P):
 seen={next(iter(P))};todo=list(seen)
 for x,y in todo:
  for q in [(x+1,y),(x-1,y),(x,y+1),(x,y-1)]:
   if q in P and q not in seen: seen.add(q);todo.append(q)
 return len(seen)==len(P)
# Every u-monotone length-10 walk: only 2^10, no animal enumeration.
rows=[];hist=collections.Counter()
for steps in itertools.product([-1,1],repeat=10):
 x=y=0;P={(x,y)}
 for d in steps:
  x+=d==1;y+=d==-1;P.add((x,y))
 g=good(P);assert g
 hist[len(g)]+=1
 rows.append({'steps':''.join('E' if d==1 else 'N' for d in steps),'center':g[0]})
# Radius-4 five-shift claim counterexample, enumerate subsets of collision cells only.
S=[(0,0),(1,0),(-1,0),(0,1),(0,-1)]
D4={(x,y) for x in range(-4,5) for y in range(-4,5) if abs(x)+abs(y)<=4}
constraints=[{(a+x,b+y) for a,b in H}&D4 for x,y in S]
sets={frozenset()}
for c in constraints:
 sets={p|{q} for p in sets for q in c}
 sets={p for p in sets if not any(q<p for q in sets)}
minimal=sorted(sets,key=lambda p:(len(p),sorted(p)))
# Fixed-terminal exact Steiner subset DP over D4 (obstacles none), at most 5 terminals.
def steiner(T):
 V=sorted(D4);idx={p:i for i,p in enumerate(V)};n=len(V);adj=[[idx[q] for q in V if abs(p[0]-q[0])+abs(p[1]-q[1])==1] for p in V]
 dp=[[99]*n for _ in range(1<<len(T))];parent={}
 for i,t in enumerate(T):dp[1<<i][idx[t]]=0
 for m in range(1,1<<len(T)):
  a=(m-1)&m
  while a:
   b=m^a
   if b:
    for v in range(n):
     z=dp[a][v]+dp[b][v]
     if z<dp[m][v]:dp[m][v]=z;parent[m,v]=('split',a,b)
   a=(a-1)&m
  import heapq
  queue=[(d,v) for v,d in enumerate(dp[m])];heapq.heapify(queue)
  while queue:
   d,v=heapq.heappop(queue)
   if d!=dp[m][v]:continue
   for w in adj[v]:
    if d+1<dp[m][w]:dp[m][w]=d+1;parent[m,w]=('edge',v);heapq.heappush(queue,(d+1,w))
 m=(1<<len(T))-1;v=min(range(n),key=dp[m].__getitem__);val=dp[m][v];used=set()
 def recover(m,v):
  used.add(V[v]);p=parent.get((m,v))
  if p:
   if p[0]=='edge':recover(m,p[1])
   else:recover(p[1],v);recover(p[2],v)
 recover(m,v);assert connected(used);assert set(T)<=used;assert len(used)<=val+1
 return val+1,used
best=None
for T in minimal:
 n,P=steiner(sorted(T))
 if best is None or n<best[0]:best=(n,P,T)
n,P,T=best
assert all(any((x-a,y-b) in H for x,y in P) for a,b in S)
out={'monotone_walks':len(rows),'monotone_good_center_histogram':dict(sorted(hist.items())),'minimal_five_shift_hitting_sets':len(minimal),'hitting_set_size_histogram':dict(collections.Counter(map(len,minimal))),'minimum_connected_five_shift_blocker_size':n,'blocker':sorted(P),'terminals':sorted(T),'other_good_centers':good(P),'five_centers':S}
open(L+'/exploration.json','w').write(json.dumps(out,indent=2)+'\n');open(L+'/monotone-certificate.json','w').write(json.dumps(rows,separators=(',',':'))+'\n');print(json.dumps(out,indent=2))
