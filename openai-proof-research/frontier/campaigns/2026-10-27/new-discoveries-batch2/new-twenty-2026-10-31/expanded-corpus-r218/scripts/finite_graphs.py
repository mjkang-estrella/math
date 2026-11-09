from pathlib import Path
import json,itertools,time,sys
D=Path(__file__).resolve().parents[1]
def mc(a):
 n=len(a);good=[False]*(1<<n);good[0]=True
 for s in range(1,1<<n):good[s]=all(2*(a[v]&s).bit_count()>=a[v].bit_count() for v in range(n) if s>>v&1)
 dp=[-100]*(1<<n);dp[0]=0
 for s in range(1,1<<n):
  v=s&-s;t=s
  while t:
   if t&v and good[t]:dp[s]=max(dp[s],1+dp[s^t])
   t=(t-1)&s
 return dp[-1]
def connected(a,s=None):
 if s is None:s=(1<<len(a))-1
 if not s:return True
 seen=s&-s;old=0
 while old!=seen:
  old=seen
  for v in range(len(a)):
   if seen>>v&1:seen|=a[v]&s
 return seen==s
def conn(a,k):
 n=len(a)
 return n>k and all(connected(a,((1<<n)-1)^sum(1<<v for v in t)) for j in range(k) for t in itertools.combinations(range(n),j))
def removable(a,k,t):
 def rec(avail,edges):
  if len(edges)==t:
   b=a.copy()
   for u,v in edges:b[u]^=1<<v;b[v]^=1<<u
   return conn(b,k)
  if avail.bit_count()<2*(t-len(edges)):return False
  u=(avail&-avail).bit_length()-1;rest=avail^(1<<u)
  return any(rec(rest^(1<<v),edges+[(u,v)]) for v in range(len(a)) if rest>>v&1 and a[u]>>v&1) or rec(rest,edges)
 return rec((1<<len(a))-1,[])
rows=[]
for n in range(2,7):
 es=list(itertools.combinations(range(n),2));counts={'n':n,'labelled_graphs':0,'critical_graphs':0,'spectral_connected':0,'removability_instances':0};bad=[]
 for code in range(1<<len(es)):
  a=[0]*n
  for j,(u,v) in enumerate(es):
   if code>>j&1:a[u]|=1<<v;a[v]|=1<<u
  counts['labelled_graphs']+=1;m=code.bit_count()
  if m>=2:
   c=mc(a);vals=[]
   for u,v in es:
    if a[u]>>v&1:
     b=a.copy();b[u]^=1<<v;b[v]^=1<<u;vals.append(mc(b))
   if all(v!=c for v in vals):
    counts['critical_graphs']+=1
    if min(vals)<c<max(vals):bad.append({'id':374340,'code':code,'mc':c,'deleted':vals})
  if not connected(a):continue
  counts['spectral_connected']+=1
  deg=[v.bit_count() for v in a];rhs=0.
  for u,v in es:
   if not a[u]>>v&1:continue
   c=2
   for s in range(1<<n):
    if s>>u&1 and s>>v&1 and all(((a[z]|(1<<z))&s)==s for z in range(n) if s>>z&1):c=max(c,s.bit_count())
   rhs+=2*(1-1/c)*(1/deg[u]+1/deg[v])
  x=[1.]*n;q=0.
  for it in range(35):
   y=[deg[u]*x[u]+sum(x[v] for v in range(n) if a[u]>>v&1) for u in range(n)];q=sum(x[u]*y[u] for u in range(n))/sum(v*v for v in x);mx=max(y);x=[v/mx for v in y]
  if q>rhs+1e-8:bad.append({'id':374894,'code':code,'rayleigh_float':q,'rhs_float':rhs})
  delta=min(deg)
  for k in range(3,delta):
   if conn(a,k):
    counts['removability_instances']+=1
    if not (delta%2==0 and m==n*(n-1)//2) and not removable(a,k,(delta+2)//2):bad.append({'id':374904,'code':code,'k':k})
 counts['violations']=bad;rows.append(counts);print(json.dumps(counts),flush=True)
 (D/'logs/finite-graphs-results.json').write_text(json.dumps(rows,indent=2))
