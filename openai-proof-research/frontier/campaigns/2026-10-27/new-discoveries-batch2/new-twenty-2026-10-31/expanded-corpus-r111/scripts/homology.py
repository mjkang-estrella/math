import itertools,math,json,pathlib,numpy as np
L=pathlib.Path(__file__).resolve().parents[1]
def components(n,s):
 adj=[[]for _ in range(n)]
 for i in range(n):
  if s>>i&1:adj[i].append((i+1)%n);adj[(i+1)%n].append(i)
 groups=[];seen=set()
 for v in range(n):
  if v in seen:continue
  q={v};todo=[v];seen.add(v)
  while todo:
   u=todo.pop()
   for w in adj[u]:
    if w not in seen:seen.add(w);q.add(w);todo.append(w)
  groups.append(tuple(sorted(q)))
 return tuple(groups)
def allocations(sizes,remain):
 if not sizes:yield ();return
 for c in itertools.combinations(remain,sizes[0]):
  for tail in allocations(sizes[1:],tuple(x for x in remain if x not in c)):yield (c,)+tail
def rank(A,p):
 A=A.copy()%p;r=0
 for j in range(A.shape[1]):
  ix=np.flatnonzero(A[r:,j])
  if not len(ix):continue
  k=r+ix[0];A[[r,k]]=A[[k,r]];A[r]=A[r]*pow(int(A[r,j]),-1,p)%p
  nz=np.flatnonzero(A[:,j]);nz=nz[nz!=r]
  A[nz]=(A[nz]-A[nz,j,None]*A[r,None,:])%p;r+=1
  if r==A.shape[0]:break
 return r
out=[]
for n in range(3,6):
 co={s:components(n,s)for s in range(1<<n)};bases={i:[]for i in range(n+1)}
 for s in co:
  for a in allocations([len(c)for c in co[s]],tuple(range(n))):bases[s.bit_count()].append((s,a))
 ix={i:{x:j for j,x in enumerate(bases[i])}for i in bases};mats={}
 for d in range(1,n+1):
  A=np.zeros((len(bases[d-1]),len(bases[d])),dtype=np.int64)
  for j,(s,a) in enumerate(bases[d]):
   for e in range(n):
    if not s>>e&1:continue
    t=s^(1<<e);sign=(-1)**((s&((1<<e)-1)).bit_count());groups=co[t];old=co[s];owner={v:k for k,g in enumerate(old)for v in g}
    for b in allocations([len(g)for g in groups],tuple(range(n))):
     if all(set(a[k])==set(x for h,g in enumerate(groups)if owner[g[0]]==k for x in b[h])for k in range(len(old))):A[ix[d-1][t,b],j]+=sign
  mats[d]=A
 for d in range(2,n+1):assert not np.any(mats[d-1]@mats[d])
 for p in [2,3,5,101]:
  ranks={d:rank(A,p)for d,A in mats.items()};hh=[len(bases[d])-ranks.get(d,0)-ranks.get(d+1,0)for d in range(n+1)];row={'n':n,'field_prime':p,'chain_dimensions':[len(bases[d])for d in bases],'ranks':ranks,'homology_dimensions':hh,'conjectured':[math.comb(n-1,d)if d<n else 0 for d in range(n+1)]};out.append(row);print(row,flush=True);(L/'outputs/homology.json').write_text(json.dumps(out,indent=2))
