import pathlib,json,itertools,sys,time,collections
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]
mode=sys.argv[1];out=[];start=time.monotonic()
for n,es in json.loads((D/'outputs/atlas.json').read_text()):
 if n<3:continue
 adj=[0]*n
 for a,b in es:adj[a]|=1<<b;adj[b]|=1<<a
 def clique(s):return all(adj[v]&s==s^(1<<v) for v in range(n) if s>>v&1)
 record={'n':n,'edges':es}
 if mode=='cycle':
  cyc=set()
  def dfs(root,v,s):
   if s.bit_count()>=3 and adj[v]>>root&1:cyc.add(s)
   for w in range(root+1,n):
    if not s>>w&1 and adj[v]>>w&1:dfs(root,w,s|1<<w)
  for v in range(n):dfs(v,v,1<<v)
  sums={}
  for t in range(3,n+1):
   val=Fraction(0)
   for s in range(1,1<<n):
    if s.bit_count()!=t or not clique(s):continue
    gam=max(c.bit_count() for c in cyc if c&s==s)
    import math
    val+=Fraction(math.comb(gam,2),math.comb(gam,t))
   sums[t]=str(val)
   if val>len(es):print('COUNTEREXAMPLE',record,t,val,flush=True)
  record['sums']=sums
 elif mode=='isolation':
  result={}
  for k in range(3,min(n,5)+1):
   if n==k and len(es)==n*(n-1)//2:continue
   req=[]
   for s in range(1,1<<n):
    if s.bit_count()==k and clique(s):
     t=s
     for v in range(n):
      if s>>v&1:t|=adj[v]
     req.append(t)
   req=list(set(req));c=[-1]*n
   def rec(v,hi):
    if v==n:return c.copy()
    for x in range(min(k,hi+1)+1):
     c[v]=x
     good=True
     for t in req:
      if t>>(v+1)==0 and {c[z] for z in range(v+1) if t>>z&1}!=set(range(k+1)):good=False;break
     if good:
      sol=rec(v+1,max(hi,x))
      if sol is not None:return sol
    c[v]=-1
   sol=rec(0,-1);result[k]=sol
   if sol is None:print('COUNTEREXAMPLE',record,k,flush=True)
  record['colors']=result
 out.append(record)
(D/f'outputs/{mode}-atlas.json').write_text(json.dumps(out))
print(mode,'graphs',len(out),'by_n',dict(collections.Counter(x['n'] for x in out)),'seconds',time.monotonic()-start,flush=True)
