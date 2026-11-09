import itertools,pathlib,json,time
L=pathlib.Path(__file__).resolve().parents[1];k=5;n=11;start=time.time();paths=[]
for rise in itertools.combinations(range(1,n),k):
 h=0;w=tuple(int(j in rise) for j in range(1,n))
 for b in w:
  h+=2*b-1
  if h<0:break
 else:paths.append(w)
def reflect(w):return tuple(1-b for b in w[::-1])
groups=[];seen=set()
for w in paths:
 if w in seen:continue
 r=reflect(w);seen|={w,r};groups.append((w,r))
sets=list(itertools.combinations(range(n),k));idx={sum(1<<v for v in s):i for i,s in enumerate(sets)}
def cover(p):
 bits=0
 for j in range(n):
  s=sum(1<<p[(j+t)%n] for t in range(k));bits |=1<<idx[s]
 return bits
def rp(p):return (0,)+tuple((-p[-j])%n for j in range(1,n))
G=[]
for gi,(w,r) in enumerate(groups):
 up=[j for j in range(1,n) if w[j-1]];down=[j for j in range(1,n) if not w[j-1]];cand={}
 for a in itertools.permutations(range(1,k+1)):
  for b in itertools.permutations(range(k+1,n)):
   p=[0]*n
   for j,v in zip(up,a):p[j]=v
   for j,v in zip(down,b):p[j]=v
   q=rp(p)
   if w==r and tuple(p)!=q:continue
   x=cover(p);y=cover(q)
   if w!=r and x&y:continue
   mask=x|y;cand.setdefault(mask,p)
 G.append(list(cand.items()));print('group',gi,'self',w==r,'candidates',len(cand),flush=True)
# Fix the all-rise/all-fall path to identity by simultaneous sign-preserving relabeling.
gi=next(i for i,(w,r) in enumerate(groups) if w==(1,)*k+(0,)*k); identity=list(range(n));G[gi]=[(cover(identity),identity)]
full=(1<<len(sets))-1;nodes=0;solution=[]
def rec(rem,used):
 global nodes
 nodes+=1
 if nodes%1000==0 and time.time()-start>100:raise TimeoutError
 if not rem:return used==full
 best=None;pick=None
 for i in rem:
  avail=[v for v in G[i] if not(v[0]&used)]
  if not avail:return False
  if best is None or len(avail)<len(best):best=avail;pick=i
 for mask,p in best:
  solution.append((pick,p))
  if rec(rem-{pick},used|mask):return True
  solution.pop()
 return False
try:status='SAT' if rec(set(range(len(G))),0) else 'UNSAT'
except TimeoutError:status='UNKNOWN_WALL_BUDGET'
print('RESULT',status,'nodes',nodes,flush=True);(L/'outputs/wreath5.json').write_text(json.dumps({'k':k,'group_candidate_counts':[len(g) for g in G],'nodes':nodes,'status':status,'solution':solution if status=='SAT' else []},indent=2))
