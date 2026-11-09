import itertools as it,random,json,time,resource
resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));random.seed(5402);t=time.monotonic()
def proper(adj,k):
 n=len(adj)
 def rec(C,v):
  if v==n:
   if len(C)==k:yield C
   return
  for j,x in enumerate(C):
   if not adj[v]&x:yield from rec(C[:j]+[x|1<<v]+C[j+1:],v+1)
  if len(C)<k:yield from rec(C+[1<<v],v+1)
 yield from rec([],0)
def isirc(adj,C):
 for vs in it.product(*[[v for v in range(len(adj)) if x>>v&1] for x in C]):
  S=sum(1<<v for v in vs)
  for v in vs:
   if adj[v]&S and not any((a|1<<w)&S==1<<v for w,a in enumerate(adj)):return False
 return True
stats={};witness=None;merge_obstruction=None
for n in [8,9,10,11,12]:
 for z in range(300):
  p=random.choice([.3,.5,.7,.9]);adj=[0]*n;edges=[]
  for u,v in it.combinations(range(n),2):
   if u%3!=v%3 and random.random()<p:adj[u]|=1<<v;adj[v]|=1<<u;edges.append((u,v))
  if min(map(int.bit_count,adj))<2:continue
  hastriangle=any(adj[u]>>v&1 and adj[u]&adj[v] for u in range(n) for v in range(u+1,n))
  if not hastriangle:continue
  stats[n]=stats.get(n,0)+1
  c3=next((C for C in proper(adj,3) if isirc(adj,C)),None)
  if c3 is None:
   c4=next((C for C in proper(adj,4) if isirc(adj,C)),None)
   if c4 is not None:witness={'n':n,'edges':edges,'irc4':c4};break
  if time.monotonic()-t>55:break
 if witness or time.monotonic()-t>55:break
print(json.dumps({'route':'360705 planted tripartite graphs with triangle (chi=3)','tested':stats,'counterexample':witness,'seconds':time.monotonic()-t}),flush=True)
def q(S):
 C={}
 for a,b in it.combinations(S,2):C[a^b]=C.get(a^b,0)+1
 return sum(x*(x-1)//2 for x in C.values())//3
def rank(S):
 B={}
 for a in S:
  a^=S[0]
  while a:
   k=a.bit_length()
   if k in B:a^=B[k]
   else:B[k]=a;break
 return len(B)
res=[]
for dim in [5,6]:
 N=1<<dim
 for l in [6,7,8,9,12,15,16,17,24,31,32]:
  if l>=N or (l-1).bit_length()>=dim:continue
  target=q(list(range(l-1)));best=-1;bestS=None;trials=0
  for restart in range(15):
   S=sorted(random.sample(range(N),l))
   while rank(S)<=(l-1).bit_length():S=sorted(random.sample(range(N),l))
   score=q(S)
   for step in range(150):
    T=S.copy();T.remove(random.choice(T));T.append(random.choice([a for a in range(N) if a not in S]));T.sort()
    if rank(T)<=(l-1).bit_length():continue
    z=q(T);trials+=1
    if z>=score or random.random()<.01:S=T;score=z
    if score>best:best=score;bestS=S
  res.append({'dim':dim,'l':l,'lex_lower_bound_for_Q_lminus1':target,'best_outside_quads':best,'exceeds_lower_bound_only':best>target,'trials':trials,'set':bestS})
print(json.dumps({'route':'360371 affine-rank-constrained local search; no global upper bound certified','results':res,'seconds':time.monotonic()-t}),flush=True)
