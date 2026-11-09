import itertools,json,math,pathlib,sys

D=pathlib.Path(__file__).resolve().parents[1]
def perm(n):
 ps=list(itertools.permutations(range(n)));idx={p:i for i,p in enumerate(ps)}
 def mul(a,b):return tuple(a[b[i]] for i in range(n))
 def inv(a):return tuple(a.index(i) for i in range(n))
 def singular(a):
  seen=set()
  for i in range(n):
   if i in seen:continue
   j=i;k=0
   while j not in seen: seen.add(j);k+=1;j=a[j]
   if k%2==0:return True
  return False
 return ps,idx,mul,inv,singular
def gl(n,q):
 ps=[]
 def mul(a,b):return tuple(sum(a[i*n+k]*b[k*n+j] for k in range(n))%q for i in range(n) for j in range(n))
 ident=tuple(int(i==j) for i in range(n) for j in range(n))
 for a in itertools.product(range(q),repeat=n*n):
  rows=[list(a[i*n:i*n+n]) for i in range(n)]; rank=0
  for j in range(n):
   pivot=next((k for k in range(rank,n) if rows[k][j]),None)
   if pivot is None:continue
   rows[rank],rows[pivot]=rows[pivot],rows[rank];z=pow(rows[rank][j],-1,q);rows[rank]=[v*z%q for v in rows[rank]]
   for k in range(n):
    if k!=rank:
     z=rows[k][j];rows[k]=[(v-z*w)%q for v,w in zip(rows[k],rows[rank])]
   rank+=1
  if rank==n:ps.append(a)
 idx={p:i for i,p in enumerate(ps)}
 def inv(a):
  b=ident
  for _ in range(len(ps)):
   if mul(a,b)==ident:return b
   b=mul(a,b)
 def singular(a):
  b=a;o=1
  while b!=ident:b=mul(a,b);o+=1
  return o%q==0
 return ps,idx,mul,inv,singular
kind=sys.argv[1];n=int(sys.argv[2]);q=int(sys.argv[3]) if len(sys.argv)>3 else None
ps,idx,mul,inv,singular=perm(n) if kind=='S' else gl(n,q)
adj=[0]*len(ps); invs=[inv(b) for b in ps]
for i,a in enumerate(ps):
 for j in range(i):
  if singular(mul(a,invs[j])):adj[i]|=1<<j;adj[j]|=1<<i
e=idx[tuple(range(n)) if kind=='S' else tuple(int(i==j) for i in range(n) for j in range(n))]
best=0;count=0;bad=[];maximal=0

def bits(x):
 while x:
  b=x&-x;yield b.bit_length()-1;x^=b

def bk(c,P,X):
 global best,count,bad,maximal
 if not (P|X):
  maximal+=1
  if len(c)<best:return
  if len(c)>best:best=len(c);count=0;bad=[]
  count+=1;cs=set(c)
  if any(idx[mul(ps[a],ps[b])] not in cs for a in c for b in c):bad.append(c)
  return
 if len(c)+P.bit_count()<best:return
 u=max(bits(P|X),key=lambda v:(P&adj[v]).bit_count())
 for v in list(bits(P&~adj[u])):
  bk(c+[v],P&adj[v],X&adj[v]);P &= ~(1<<v); X |= 1<<v
bk([e],adj[e],0)
r=dict(kind=kind,n=n,q=q,order=len(ps),edges=sum(a.bit_count() for a in adj)//2,max_size=best,normalized_maxima=count,maximal_containing_identity=maximal,nonsubgroup_maxima=len(bad),witness=[ps[i] for i in bad[0]] if bad else None)
print(json.dumps(r),flush=True);(D/f'outputs/groups-{kind}-{n}-{q}.json').write_text(json.dumps(r,indent=2)+'\n')
