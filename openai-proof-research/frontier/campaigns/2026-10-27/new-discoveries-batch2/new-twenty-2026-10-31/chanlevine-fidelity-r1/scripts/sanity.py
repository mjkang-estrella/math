"""Independent source-dynamics SCC check and exact proof-formula comparison.
Natural fixed-level space is finite and forward closed. Definition 5.2 recurrence
is precisely membership in a terminal SCC with a nonempty execution: a terminal
SCC can reach every state sharing a descendant, whereas a nonterminal SCC cannot
return from a reachable downstream terminal SCC. Positive level ensures an edge.
A second bounded signed test uses x>=-1, also forward closed.
"""
import itertools, json, math
from pathlib import Path

def compositions(total,n):
 if n==1: yield (total,); return
 for a in range(total+1):
  for rest in compositions(total-a,n-1): yield (a,)+rest

def direct(n,m,lower=0):
 states=[(tuple(v+lower for v in x),q) for x in compositions(m-n*lower,n) for q in itertools.product((False,True),repeat=n)]
 index={s:k for k,s in enumerate(states)}; adj=[]; rev=[[] for _ in states]
 for k,(x,q) in enumerate(states):
  row=[]
  for v in range(n):
   if x[v]<=0:continue
   y=list(x); z=list(q); y[v]-=1; y[(v+(-1 if q[v] else 1))%n]+=1; z[v]=not z[v]
   t=index[(tuple(y),tuple(z))]; row.append(t); rev[t].append(k)
  adj.append(row)
 seen=set(); order=[]
 for v in range(len(states)):
  if v in seen:continue
  seen.add(v); stack=[(v,0)]
  while stack:
   a,j=stack[-1]
   if j==len(adj[a]):order.append(a);stack.pop();continue
   stack[-1]=(a,j+1);b=adj[a][j]
   if b not in seen:seen.add(b);stack.append((b,0))
 comp=[-1]*len(states); groups=[]
 for v in reversed(order):
  if comp[v]>=0:continue
  cid=len(groups);g=[];stack=[v];comp[v]=cid
  while stack:
   a=stack.pop();g.append(a)
   for b in rev[a]:
    if comp[b]<0:comp[b]=cid;stack.append(b)
  groups.append(g)
 terminals=[g for cid,g in enumerate(groups) if all(comp[b]==cid for a in g for b in adj[a]) and any(adj[a] for a in g)]
 counts=[0]*n
 recurrent=set(a for g in terminals for a in g)
 for g in terminals:
  assert all(any(states[a][0][v]>0 for a in g) for v in range(n)) # all letters occur on internal edges
  weights={(sum(k*x[k] for k in range(n))+q.count(False))%n for a in g for x,q in [states[a]]}
  assert len(weights)==1;counts[weights.pop()]+=len(g)
 assert len(terminals)==n
 for a,(x,q) in enumerate(states):
  cycle=(min(x)>=0 and all(not(q[k] and not q[(k+1)%n]) or x[k]>0 or x[(k+1)%n]>0 for k in range(n)) and sum(x)>0)
  assert (a in recurrent)==cycle
 return counts,len(states)

def add(a,b):
 return [(a[k] if k<len(a) else 0)+(b[k] if k<len(b) else 0) for k in range(max(len(a),len(b)))]
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def mu(n):
 s=1;p=2
 while p*p<=n:
  if n%p==0:
   n//=p;s=-s
   if n%p==0:return 0
   while n%p==0:n//=p
  p+=1
 return -s if n>1 else s

def formula(n,m,i):
 ans=0
 for e in range(1,math.gcd(n,m)+1):
  if n%e or m%e:continue
  q=0 if e%2 else 2*(-1)**(e//2)
  p=[2,q];det=[1,-2,1];a=[2];b=p
  for _ in range(2,n//e+1):a,b=b,add(mul(p,b),[-v for v in mul(det,a)])
  v=b if n//e else a; r=n//e; h=m//e
  w=sum(v[k]*math.comb(r+h-k-1,h-k) for k in range(min(h,len(v)-1)+1))
  ram=sum(d*mu(e//d) for d in range(1,e+1) if math.gcd(e,i)%d==0)
  ans+=w*ram
 assert ans%n==0
 return ans//n

rows=[]
for n in range(3,7):
 for m in range(1,5):
  counts,size=direct(n,m); expected=[formula(n,m,i) for i in range(n)]
  assert counts==expected,(n,m,counts,expected)
  row=dict(n=n,m=m,states=size,counts=counts,formula=expected);rows.append(row);print(json.dumps(row),flush=True)
for n in (3,4):
 for m in (1,2):
  counts,size=direct(n,m,-1);assert counts==[formula(n,m,i) for i in range(n)]
  row=dict(n=n,m=m,lower=-1,states=size,counts=counts);rows.append(row);print(json.dumps(row),flush=True)
Path('../logs/sanity-results.json').write_text(json.dumps(rows,indent=2)+'\n')
print('PASS: 16 natural and 4 signed cases, SCC/cycle-test/formula agree')
