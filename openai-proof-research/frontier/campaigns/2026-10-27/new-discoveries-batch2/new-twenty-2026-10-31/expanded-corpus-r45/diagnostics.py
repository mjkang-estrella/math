import os,resource,json,math,random,time,pathlib
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);O=pathlib.Path(__file__).resolve().parent

def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b))) ]
def sub(a,b):return add(a,[-v for v in b])
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def poly(E,n,deleted=-1):
 adj=[[] for _ in range(n)]
 for a,b in E:
  if deleted not in (a,b):adj[a].append(b);adj[b].append(a)
 root=next(i for i in range(n) if i!=deleted)
 def dfs(v,p):
  s=[1];tot=[1];u=[1]
  for w in adj[v]:
   if w==p:continue
   S,D,U=dfs(w,v);s=mul(s,add(add(S,D),U));tot=mul(tot,add(S,D));u=mul(u,D)
  return [0]+s,sub(tot,u),u
 s,d,u=dfs(root,-1);return add(s,d)
def mode(a):return max(i for i,v in enumerate(a) if v==max(a))
def unimodal(a):
 m=mode(a);return all(a[i]<=a[i+1] for i in range(m)) and all(a[i]>=a[i+1] for i in range(m,len(a)-1))
def trees():
 rng=random.Random(352443);count=0;best=None;start=time.time()
 # Exact state DP first independently checked by brute-force subsets.
 for n in range(2,11):
  E=[(i,rng.randrange(i)) for i in range(1,n)];p=poly(E,n);q=[0]*(n+1)
  for mask in range(1<<n):
   cov=mask
   for a,b in E:
    if mask>>a&1:cov|=1<<b
    if mask>>b&1:cov|=1<<a
   if cov==(1<<n)-1:q[mask.bit_count()]+=1
  assert p==q,(p,q)
 for trial in range(1600):
  n=rng.randrange(5,101);kind=trial%4
  if kind==0:E=[(i,rng.randrange(i)) for i in range(1,n)]
  elif kind==1:E=[(i,max(0,i-rng.randrange(1,min(i,5)+1))) for i in range(1,n)]
  elif kind==2:E=[(i,rng.randrange(min(i,1+trial%8))) for i in range(1,n)]
  else:
   E=[]
   for i in range(1,n):E.append((i,0 if (i-1)%3==0 else i-1))
  deg=[0]*n
  for a,b in E:deg[a]+=1;deg[b]+=1
  p=poly(E,n)
  for v in rng.sample([i for i,x in enumerate(deg) if x==1],min(3,deg.count(1))):
   q=poly(E,n,v);count+=1;diff=abs(mode(p)-mode(q));record={'trial':trial,'n':n,'leaf':v,'edges':E,'mode':mode(p),'deleted_mode':mode(q),'unimodal':unimodal(p) and unimodal(q),'coefficients':p,'deleted_coefficients':q}
   if best is None or diff>best['gap']:best={'gap':diff,**record}
   if diff>1 and record['unimodal']:print(json.dumps({'counterexample':record}));return
 print(json.dumps({'tested_leaf_pairs':count,'tree_trials':1600,'max_gap_witness':best,'seconds':time.time()-start,'limit':'nonexhaustive deterministic families; diagnostic only'}))
def cf():
 count=0;best=(0,None);periodmax=0
 for t in range(1,301):
  for u in range(1,t+1):
   D=t*t+4*u;s=math.isqrt(D)
   if s*s==D:continue
   m,d=t,2;seen={};a=[]
   while (m,d) not in seen:
    seen[m,d]=len(a);z=(m+s)//d;a.append(z);m=z*d-m;d=(D-m*m)//d
    assert d>0
   assert seen[m,d]==0
   count+=1;periodmax=max(periodmax,len(a));w=sorted(set(a),reverse=True)
   for k,v in enumerate(w,1):
    if k*v>t:print(json.dumps({'counterexample':{'t':t,'u':u,'period':a,'rank':k,'value':v}}));return
    r=k*v/t
    if k>1 and r>best[0]:best=(r,{'t':t,'u':u,'period':a,'rank':k,'value':v})
 print(json.dumps({'quadratic_integers_tested':count,'trace_range':[1,300],'u_range':'1..t','max_period':periodmax,'best_nontrivial_ratio':best,'limit':'exact integer arithmetic diagnostic, no Lean certification or general theorem'}))
if __name__=='__main__':
 import sys
 {'cf':cf,'trees':trees}[sys.argv[1]]()
