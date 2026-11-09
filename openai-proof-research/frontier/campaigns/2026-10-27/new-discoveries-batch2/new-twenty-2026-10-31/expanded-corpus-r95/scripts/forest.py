import itertools,random,json,resource,collections
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));rng=random.Random(95005)
def alpha(n,edges):
 a={tuple(range(n)):1}
 for u,v in edges:
  b=a.copy()
  for p,c in a.items():
   q=list(p);q[u],q[v]=q[v],q[u];q=tuple(q);b[q]=b.get(q,0)-c
  a={p:c for p,c in b.items() if c}
 return a
def moments(n,a):
 ident=tuple(range(n));b={ident:1};ans=[]
 for k in range(1,6):
  c=collections.defaultdict(int)
  for p,v in b.items():
   for q,w in a.items():c[tuple(p[x] for x in q)]+=v*w
  b={p:v for p,v in c.items() if v};ans.append(b.get(ident,0))
 return ans
for n in [4,5,6,7]:
 for typ in ['path','star','binary','broom']:
  edges=[(i-1,i) if typ=='path' else (0,i) if typ=='star' else ((i-1)//2,i) if typ=='binary' else (max(0,i-3),i) for i in range(1,n)]
  base=None;orders=0;bad=[]
  for rep in range(6):
   es=edges[:];rng.shuffle(es);val=moments(n,alpha(n,es));orders+=1
   if base is None:base=val
   if base!=val:bad.append({'edges':es,'moments':val})
  print(json.dumps({'n':n,'tree':typ,'orders_sampled':orders,'moments_k_1_to_5':base,'mismatches':bad,'normalization':'alpha/n!, moments divided by (n!)^k; identity coefficient, regular trace divided by n!'}),flush=True)
