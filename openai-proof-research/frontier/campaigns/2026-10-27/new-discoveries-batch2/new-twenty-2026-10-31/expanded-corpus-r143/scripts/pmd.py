import sys,time,json,functools
m,n=map(int,sys.argv[1:]); N=m*n
E=sorted({tuple(sorted((i*n+j,((i+1)%m)*n+j))) for i in range(m) for j in range(n)}|{tuple(sorted((i*n+j,i*n+(j+1)%n))) for i in range(m) for j in range(n)})
inc=[0]*N
for i,(u,v) in enumerate(E):inc[u]|=1<<i;inc[v]|=1<<i
M=[]
def gen(i,used,bits):
 if i==len(E):
  if bits:M.append((bits,used))
  return
 gen(i+1,used,bits)
 u,v=E[i];uv=(1<<u)|(1<<v)
 if not used&uv:gen(i+1,used|uv,bits|(1<<i))
gen(0,0,0);M.sort(key=lambda z:-z[0].bit_count())
print(json.dumps({'m':m,'n':n,'matchings':len(M)}),flush=True)
def pos(g,b,used):
 while b:
  found=False
  for i,(u,v) in enumerate(E):
   if b>>i&1:
    def deg(x):
     return sum(1 for j,(a,c) in enumerate(E) if g>>j&1 and ((a==x and used>>c&1) or(c==x and used>>a&1)))
    if deg(u)==1 or deg(v)==1:
     used&=~((1<<u)|(1<<v));b^=1<<i;found=True;break
  if not found:return False
 return True
nodes=0;start=time.monotonic()
@functools.lru_cache(None)
def solve(g,k):
 global nodes
 nodes+=1
 if nodes%1000==0:print(json.dumps({'nodes':nodes,'elapsed':time.monotonic()-start,'cache':solve.cache_info().currsize}),flush=True)
 if time.monotonic()-start>105:raise TimeoutError
 if not g:return ()
 ds=[(g&v).bit_count() for v in inc]
 if max(ds)>k or g.bit_count()>k*(N//2):return None
 if k==1:
  if max(ds)<=1:return (g,)
  return None
 required=sum(1<<i for i,d in enumerate(ds) if d==k)
 for b,used in M:
  if b&g!=b or used&required!=required:continue
  if (g.bit_count()-b.bit_count())>(k-1)*(N//2):continue
  if pos(g,b,used):
   a=solve(g^b,k-1)
   if a is not None:return (b,)+a
 return None
try:
 ans=solve((1<<len(E))-1,5)
 print(json.dumps({'completed':True,'five_part':ans,'edges':E,'nodes':nodes,'elapsed':time.monotonic()-start}),flush=True)
except TimeoutError:print(json.dumps({'completed':False,'nodes':nodes,'elapsed':time.monotonic()-start}),flush=True)
