import sys,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/"deps"))
import networkx as nx,itertools as it,math,json,pathlib,sys,time
from functools import lru_cache
D=pathlib.Path(__file__).resolve().parents[1]
def emit(i,o):
 (D/'outputs'/f'search-{i}.json').write_text(json.dumps(o,indent=2)+'\n');print(i,o,flush=True)
def color(G,lists):
 n=len(G);a=[None]*n
 def rec(left):
  if not left:return a.copy()
  ds={v:[x for x in lists[v] if all(a[u]!=x for u in G[v])] for v in left}
  v=min(left,key=lambda v:(len(ds[v]),-G.degree(v)))
  for x in ds[v]:
   a[v]=x;r=rec(left-{v})
   if r is not None:return r
  a[v]=None;return None
 return rec(set(range(n)))
def chrom(G):
 if len(G)==0:return 0
 for k in range(1,len(G)+1):
  if color(G,[range(k)]*len(G)) is not None:return k
mode=sys.argv[1]
if mode=='ironic':
 counts={};bad=[]
 for G in nx.graph_atlas_g():
  n=len(G);k=chrom(G);counts[n]=counts.get(n,0)+1
  if color(G,[[j*G.degree(v) for j in range(1,k+1)] for v in G]) is None:bad.append(nx.to_graph6_bytes(G,header=False).decode().strip())
 emit(345749,{'scope':'all graph atlas simple graphs, orders 0..7, up to isomorphism','counts_by_order':counts,'failures':bad})
elif mode=='cascade':
 counts={};bad=[]
 for G in nx.graph_atlas_g():
  n=len(G)
  if n>5:continue
  k=chrom(G)
  for roots in it.product(range(1,5),repeat=n):
   counts[n]=counts.get(n,0)+1
   if color(G,[[j*r for j in range(1,k+1)] for r in roots]) is None:bad.append([nx.to_graph6_bytes(G,header=False).decode().strip(),roots])
 emit(345750,{'scope':'all graph atlas graphs orders 0..5; each vertex root independently 1..4; length exact chromatic number','counts_by_order':counts,'failures':bad})
elif mode=='trees':
 counts={};bad=[]
 for n in range(1,16):
  counts[n]=0
  for G in ([nx.empty_graph(1)] if n==1 else nx.nonisomorphic_trees(n)):
   # bijective odd labels: all-different CSP
   labels=[0]*n;vs=sorted(G,key=lambda v:-G.degree(v));odd=list(range(1,2*n,2))
   def rec(j,avail):
    if j==n:return True
    v=vs[j]
    for x in avail:
     if all(labels[u]==0 or math.gcd(labels[u],x)==1 for u in G[v]):
      labels[v]=x
      if rec(j+1,avail-{x}):return True
    labels[v]=0;return False
   ok=rec(0,set(odd));counts[n]+=1
   if not ok:bad.append(nx.to_graph6_bytes(G,header=False).decode().strip())
  emit(355743,{'scope':f'all nonisomorphic unrooted trees of orders 1..{n}; backtracking bijections onto odd integers 1..2n-1','counts_by_order':counts,'failures':bad})
elif mode=='grid':
 def rem(a,b):
  while a and a.bit_length()>=b.bit_length():a^=b<<(a.bit_length()-b.bit_length())
  return a
 def gcd(a,b):
  while b:a,b=b,rem(a,b)
  return a
 def shift(a):
  b=0;j=0
  while a:
   if a&1:
    s=j
    while True:
     b^=1<<s
     if s==0:break
     s=(s-1)&j
   a>>=1;j+=1
  return b
 def fib(n):
  a,b=0,1
  for _ in range(n):a,b=b,(b<<1)^a
  return a
 vals=[]
 for k in range(1,10):
  n=2*3**k-1;f=fib(n+1);g=gcd(f,shift(f));vals.append([k,n,g.bit_length()-1]);emit(353680,{'definition':'d_n = deg gcd(f_(n+1)(x), f_(n+1)(x+1)) over F2; f0=0 f1=1 f(n+2)=x f(n+1)+f(n)','scope':'k=1..'+str(k),'values':vals})
elif mode=='prisms':
 vals=[]
 for k in range(3,16):
  for n in range(1,5):
   N=k*n;G=nx.Graph();G.add_nodes_from(range(N));G.add_edges_from((i*k+j,i*k+(j+1)%k) for i in range(n) for j in range(k));G.add_edges_from((i*k+j,(i+1)*k+j) for i in range(n-1) for j in range(k));a=[0]*N;vs=sorted(G,key=lambda v:-G.degree(v));nodes=[0]
   def rec(z,avail):
    nodes[0]+=1
    if nodes[0]>100000:return None
    if z==N:return a.copy()
    v=vs[z]
    for x in sorted(avail):
     if all(a[u]==0 or math.gcd(a[u],x)==1 for u in G[v]):
      a[v]=x;r=rec(z+1,avail-{x})
      if r:return r
    a[v]=0;return None
   r=rec(0,set(range(1,2*N,2)));vals.append({'k':k,'n':n,'search_nodes':nodes[0],'witness':r,'outcome':'witness' if r else 'capped_unresolved'})
   emit(355742,{'scope':'structured cases k=3..15 n=1..4; cap 100000 recursion nodes per instance; incomplete instances explicit','cases':vals})
