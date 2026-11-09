import itertools,random,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(229)
def rank2(rows):
 b={}
 for x in rows:
  while x:
   p=x.bit_length()-1
   if p not in b:b[p]=x;break
   x^=b[p]
 return len(b)
def rankp(a,p=1000003):
 a=[r[:] for r in a];r=0
 for j in range(len(a[0])):
  q=next((i for i in range(r,len(a)) if a[i][j]%p),None)
  if q is None:continue
  a[r],a[q]=a[q],a[r]; inv=pow(a[r][j],-1,p);a[r]=[v*inv%p for v in a[r]]
  for i in range(r+1,len(a)):
   v=a[i][j]%p
   if v:a[i]=[(x-v*y)%p for x,y in zip(a[i],a[r])]
  r+=1
  if r==len(a):break
 return r
def conn(n,es,removed):
 left=set(range(n))-set(removed)
 if not left:return True
 seen={min(left)};q=list(seen)
 for v in q:
  for w in left-seen:
   if tuple(sorted((v,w))) in es:seen.add(w);q.append(w)
 return seen==left
out=[];extended='--extended' in sys.argv
for n in ([10] if extended else [6,8,10]):
 ts=[t for t in itertools.combinations(range(n),3) if len({v//2 for v in t})==3];ti={t:i for i,t in enumerate(ts)}
 es=list(itertools.combinations(range(n),2));ei={e:i for i,e in enumerate(es)}
 bdy=[sum(1<<ei[e] for e in itertools.combinations(t,2)) for t in ts]
 orbits=[(i,ti[tuple(sorted(v^1 for v in t))]) for i,t in enumerate(ts) if i<ti[tuple(sorted(v^1 for v in t))]]
 basis={};ker=[]
 for j,(a,b) in enumerate(orbits):
  x=bdy[a]^bdy[b];y=1<<j
  while x:
   p=x.bit_length()-1
   if p not in basis:basis[p]=(x,y);break
   u,v=basis[p];x^=u;y^=v
  if not x:ker.append(y)
 total=(1<<len(ker))-1;limit=min(total,100000 if extended else 3000) if n==10 else total
 counters={'n':n,'orbits':len(orbits),'cycle_space_dimension':len(ker),'nonzero_cycles':total,'examined':0,'full_vertex_minimal_circuits':0,'four_connected_dense_nonplanar':0,'rank_failures':[]}
 for kk in range(1,limit+1):
  z=kk if limit==total else rng.randrange(1,total+1);mask=0
  for i,k in enumerate(ker):
   if z>>i&1:mask^=k
  inds=[v for j,pair in enumerate(orbits) if mask>>j&1 for v in pair];counters['examined']+=1
  if set(v for i in inds for v in ts[i])!=set(range(n)) or rank2([bdy[i] for i in inds])!=len(inds)-1:continue
  counters['full_vertex_minimal_circuits']+=1
  edges=set(e for i in inds for e in itertools.combinations(ts[i],2))
  if len(edges)<=3*n-6 or not all(conn(n,edges,r) for k in range(4) for r in itertools.combinations(range(n),k)):continue
  counters['four_connected_dense_nonplanar']+=1
  pts=[]
  for i in range(n//2):
   x,y,z=[rng.randrange(1,1000) for _ in range(3)];pts += [(x,y,z),(x,-y,-z)]
  mat=[]
  for u,v in edges:
   row=[0]*(3*n)
   for j in range(3):row[3*u+j]=pts[u][j]-pts[v][j];row[3*v+j]=-row[3*u+j]
   mat.append(row)
  r=rankp(mat)
  if r<3*n-6:counters['rank_failures'].append({'triangles':[ts[i] for i in inds],'rank':r})
 print(counters,flush=True);out.append(counters)
(D/('evidence/symmetric-extended.json' if extended else 'evidence/symmetric-search.json')).write_text(json.dumps(out,indent=2))
