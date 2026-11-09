import pathlib,json,functools,sys
D=pathlib.Path(__file__).resolve().parents[1];dirs=[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
def canon(c):
 variants=[]
 for reflected in [False,True]:
  a=[(r,q) if reflected else (q,r) for q,r in c]
  for _ in range(6):
   a=[(-r,q+r) for q,r in a];mq=min(q for q,r in a);mr=min(r for q,r in a);variants.append(tuple(sorted((q-mq,r-mr) for q,r in a)))
 return min(variants)
def hole(c):
 lo=-2;hi=max(max(q,r) for q,r in c)+2;space={(q,r) for q in range(lo,hi+1) for r in range(lo,hi+1)}-set(c);seen={(lo,lo)};queue=[(lo,lo)]
 for q,r in queue:
  for dq,dr in dirs:
   v=(q+dq,r+dr)
   if v in space and v not in seen:seen.add(v);queue.append(v)
 return len(seen)!=len(space)
def polynomial(c):
 vertices={};faces=[];edges=set();offset=[(2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1)]
 for q,r in c:
  f=[]
  for x,y in offset:
   v=(3*q+x,q+2*r+y)
   if v not in vertices:vertices[v]=len(vertices)
   f.append(vertices[v])
  faces.append(sum(1<<v for v in f))
  for i in range(6):edges.add(tuple(sorted((f[i],f[(i+1)%6]))))
 n=len(vertices);adj=[0]*n
 for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
 @functools.lru_cache(None)
 def match(mask):
  if not mask:return 1
  # min residual degree heuristic
  u=min((v for v in range(n) if mask>>v&1),key=lambda v:(adj[v]&mask).bit_count());bit=1<<u;other=adj[u]&mask;ans=0
  while other:
   b=other&-other;other-=b;ans+=match(mask^bit^b)
  return ans
 coeff=[0]*(len(c)+1)
 def rec(i,used,k):
  if i==len(c):coeff[k]+=match(((1<<n)-1)^used);return
  rec(i+1,used,k)
  if not used&faces[i]:rec(i+1,used|faces[i],k+1)
 rec(0,0,0)
 while coeff and coeff[-1]==0:coeff.pop()
 return coeff
cur={((0,0),)};rows=[]
for size in range(1,int(sys.argv[1])+1):
 count=0;perfect=0
 for c in sorted(cur):
  if hole(c):continue
  count+=1;a=polynomial(c)
  if not a:continue
  perfect+=1;fall=False
  for i in range(1,len(a)):
   if a[i]<a[i-1]:fall=True
   if fall and a[i]>a[i-1]:print('COUNTEREXAMPLE',c,a,flush=True);raise SystemExit
 row={'hexagons':size,'free_polyhexes':len(cur),'hole_free_checked':count,'with_perfect_matching':perfect};rows.append(row);print(row,flush=True)
 (D/f'hex-progress-{sys.argv[1]}.json').write_text(json.dumps(rows,indent=2))
 if size<int(sys.argv[1]):
  nxt=set()
  for c in cur:
   s=set(c)
   for q,r in c:
    for dq,dr in dirs:
     v=(q+dq,r+dr)
     if v not in s:nxt.add(canon(s|{v}))
  cur=nxt
(D/f'hex-results-{sys.argv[1]}.json').write_text(json.dumps(rows,indent=2))
