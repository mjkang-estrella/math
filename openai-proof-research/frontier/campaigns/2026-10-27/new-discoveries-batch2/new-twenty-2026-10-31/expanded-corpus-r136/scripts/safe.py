import sys,pathlib,json,random,itertools
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(136)
def patterns(n,k):
 def rec(a,m):
  if len(a)==n:
   if a[-1]!=0:yield tuple(a)
   return
  for c in range(min(m+2,k)):
   if c!=a[-1]:yield from rec(a+[c],max(m,c))
 yield from rec([0],0)
def bad(a,k):
 n=len(a)
 if len(set(a))==k:return True
 F={}
 for i in range(n):
  s=set()
  for d in range(n):
   j=(i+d)%n;s.add(a[j]);F[i,j]=s.copy()
 for p,q in itertools.combinations(range(n),2):
  if len(F[p,q]&F[q,p])>=k-1:return True
 for p,q,r in itertools.combinations(range(n),3):
  if len(F[p,q]&F[q,r]&F[r,p])>=k-2:return True
 return False
def good(a,k):
 colors=set(a);n=len(a)
 if len(colors)<=k-3:return True
 for A in itertools.combinations(colors,k-4):
  A=set(A)
  cuts=2 if len(colors)==k-2 else 3
  for inds in itertools.combinations(range(n),cuts):
   if all(len({a[t%n] for t in range(inds[j],inds[(j+1)%cuts]+(n if j==cuts-1 else 0))}-A)==1 for j in range(cuts)):return True
 return False
def graph(n,extra):
 edges={tuple(sorted((i,(i+1)%n))) for i in range(n)};faces=[]
 for i in range(n):edges.add((i,n));faces.append((i,(i+1)%n,n))
 for v in range(n+1,n+extra):
  f=faces.pop(rng.randrange(len(faces)))
  edges.update(tuple(sorted((u,v))) for u in f);faces.extend((v,f[j],f[(j+1)%3]) for j in range(3))
 # Flip interior edges with two incident triangular faces; preserves the disk and boundary.
 for _ in range(10*(n+extra)):
  incidence={}
  for ix,f in enumerate(faces):
   for j in range(3):incidence.setdefault(tuple(sorted((f[j],f[(j+1)%3]))),[]).append(ix)
  e=rng.choice(list(edges));fs=incidence.get(e,[])
  if len(fs)!=2:continue
  a,b=e;c=next(v for v in faces[fs[0]] if v not in e);d=next(v for v in faces[fs[1]] if v not in e);ne=tuple(sorted((c,d)))
  if c==d or ne in edges or (c<n and d<n):continue
  edges.remove(e);edges.add(ne);faces[fs[0]]=(c,d,a);faces[fs[1]]=(c,d,b)
 adj=[set() for _ in range(n+extra)]
 for u,v in edges:adj[u].add(v);adj[v].add(u)
 return adj
def extends(adj,a,k):
 col=dict(enumerate(a));todo=set(range(len(a),len(adj)))
 def rec():
  if not todo:return True
  choices=[(set(range(k))-{col[v] for v in adj[u] if v in col},u) for u in todo];cs,u=min(choices,key=lambda x:len(x[0]))
  if not cs:return False
  todo.remove(u)
  for c in cs:
   col[u]=c
   if rec():return True
  col.pop(u,None);todo.add(u);return False
 return rec()
out=[]
for n in range(3,12):
 ps=[];total=nonbad=ng=checks=0
 for a in patterns(n,6):
  total+=1
  if not bad(a,6):
   nonbad+=1
   if not good(a,6):ng+=1;ps.append(a)
 if len(ps)>250:ps=rng.sample(ps,250)
 for extra in [1,2,4,6,8,10,14]:
  for rep in range(4):
   adj=graph(n,extra)
   for a in ps:
    checks+=1
    if not extends(adj,a,6):
     result={'n':n,'adj':[sorted(s) for s in adj],'boundary':a};(D/'outputs/safe-candidate.json').write_text(json.dumps(result));print('CANDIDATE',result,flush=True);raise SystemExit
 record={'cycle_length':n,'canonical_color_patterns':total,'not_bad':nonbad,'not_bad_not_good':ng,'patterns_tested':len(ps),'disk_extension_tests':checks};print(json.dumps(record),flush=True);out.append(record)
(D/'outputs/safe.json').write_text(json.dumps(out,indent=2)+'\n')
