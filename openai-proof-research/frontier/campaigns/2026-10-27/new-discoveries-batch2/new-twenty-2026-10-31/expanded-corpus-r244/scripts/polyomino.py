import itertools,functools,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];dirs=[(1,0),(-1,0),(0,1),(0,-1)]
def canon(c):
 out=[]
 for refl in [False,True]:
  a=[(y,x) if refl else (x,y) for x,y in c]
  for _ in range(4):
   a=[(-y,x) for x,y in a];mx=min(x for x,y in a);my=min(y for x,y in a);out.append(tuple(sorted((x-mx,y-my) for x,y in a)))
 return min(out)
def graph(c):
 vs={};edges=set()
 for x,y in c:
  f=[]
  for dx,dy in [(0,0),(1,0),(1,1),(0,1)]:
   v=x+dx,y+dy
   if v not in vs:vs[v]=len(vs)
   f.append(vs[v])
  for i in range(4):edges.add(tuple(sorted((f[i],f[(i+1)%4]))))
 a=[set() for v in vs]
 for u,v in edges:a[u].add(v);a[v].add(u)
 return a,len(edges)
def rankdiag(a,k,prime):
 # Sparse Gaussian elimination of d: MC_(k,k) -> MC_(k-1,k).
 pivots={};cols=0
 def paths(p):
  nonlocal cols
  if len(p)<=k:
   for v in a[p[-1]]:yield from paths(p+(v,))
  else:yield p
 for u in range(len(a)):
  for p in paths((u,)):
   cols+=1;col={}
   for i in range(1,k):
    if p[i-1]!=p[i+1] and p[i+1] not in a[p[i-1]]:
     row=p[:i]+p[i+1:];col[row]=(col.get(row,0)+(-1)**i)%prime
   col={r:c for r,c in col.items() if c}
   while col:
    r=min(col)
    if r not in pivots:
     inv=pow(col[r],-1,prime);pivots[r]={t:c*inv%prime for t,c in col.items()};break
    factor=col[r]
    for t,c in pivots[r].items():
     val=(col.get(t,0)-factor*c)%prime
     if val:col[t]=val
     elif t in col:del col[t]
 return cols-len(pivots)
cur={((0,0),)};rows=[]
for s in range(1,int(sys.argv[1])+1):
 total=0
 for c in cur:
  a,e=graph(c)
  for k in range(1,5):
   target=2*e+4*(k-1)*s
   for prime in [1000003,1000033]:
    got=rankdiag(a,k,prime)
    if got!=target:print('DIAGNOSTIC MISMATCH',c,k,prime,got,target,flush=True);raise SystemExit
  total+=1
 rows.append({'squares':s,'typeI_typeII_generated':total,'k':[1,2,3,4],'fields':[1000003,1000033]});print(rows[-1],flush=True)
 nxt=set()
 for c in cur:
  cells=set(c)
  for x,y in c:
   for dx,dy in dirs:
    v=x+dx,y+dy
    if v in cells:continue
    shared=[(ex,ey) for ex,ey in dirs if (v[0]+ex,v[1]+ey) in cells]
    oldvs={(x+dx,y+dy) for x,y in cells for dx,dy in [(0,0),(1,0),(1,1),(0,1)]}
    newvs={(v[0]+dx,v[1]+dy) for dx,dy in [(0,0),(1,0),(1,1),(0,1)]}
    if len(oldvs&newvs)!=len(shared)+1:continue
    if len(shared)==1 or (len(shared)==2 and shared[0][0]!=-shared[1][0] and shared[0][1]!=-shared[1][1]):nxt.add(canon(cells|{v}))
 cur=nxt
(D/f'polyomino-results-{sys.argv[1]}.json').write_text(json.dumps(rows,indent=2))
