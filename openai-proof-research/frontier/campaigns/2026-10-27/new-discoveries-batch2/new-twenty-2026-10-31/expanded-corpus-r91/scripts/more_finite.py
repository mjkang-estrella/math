import pathlib,json,itertools,collections
D=pathlib.Path(__file__).resolve().parents[1]
def conn(adj,mask):
 if not mask:return False
 seen=mask&-mask;old=0
 while seen!=old:
  old=seen
  for i,a in enumerate(adj):
   if seen>>i&1:seen|=a&mask
 return seen==mask
# Radial graphs of embedded wheels: duals of their 4-regular medial link projections.
r=[]
for k in range(3,10):
 faces=[(0,i+1,(i+1)%k+1) for i in range(k)]+[tuple(range(1,k+1))];nv=k+1;N=nv+len(faces);adj=[0]*N
 for j,face in enumerate(faces,nv):
  for i in face:adj[i]|=1<<j;adj[j]|=1<<i
 best=0;w=0;tested=0
 for mask in range(1<<N):
  c=mask.bit_count()
  if c<=best:continue
  if any(mask>>i&1 and a&mask for i,a in enumerate(adj)):continue
  tested+=1
  if conn(adj,((1<<N)-1)^mask):best=c;w=mask
 d=dict(wheel_rim=k,crossings=2*k,dual_vertices=N,max_nonseparating_independent=best,witness=w,independent_candidates_tested=tested);r.append(d);print(d,flush=True)
(D/'outputs/nonseparating.json').write_text(json.dumps(r,indent=2)+'\n')
# All cycles in each connected labelled graph on up to four vertices; enumerate all simple-cycle bases.
r=[]
for n in range(2,5):
 edges=list(itertools.combinations(range(n),2));hist=collections.Counter();cnt=0
 for mask in range(1<<len(edges)):
  es=[e for i,e in enumerate(edges) if mask>>i&1];adj=[0]*n;ix={e:i for i,e in enumerate(es)}
  for a,b in es:adj[a]|=1<<b;adj[b]|=1<<a
  if not conn(adj,(1<<n)-1):continue
  rank=len(es)-n+1;cycles=set()
  for k in range(3,n+1):
   for vs in itertools.permutations(range(n),k):
    if vs[0]!=min(vs) or vs[1]>vs[-1]:continue
    ce=[tuple(sorted((vs[i],vs[(i+1)%k]))) for i in range(k)]
    if all(e in ix for e in ce):cycles.add(sum(1<<ix[e] for e in ce))
  best=rank
  for basis in itertools.combinations(cycles,rank):
   piv={}
   for c in basis:
    while c:
     b=c.bit_length()-1
     if b not in piv:piv[b]=c;break
     c^=piv[b]
   if len(piv)==rank:best=min(best,max([sum(c>>i&1 for c in basis) for i in range(len(es))]+[0]))
  hist[best]+=1;cnt+=1
 r.append(dict(n=n,graphs=cnt,basis_number_histogram=dict(hist)));print(r[-1],flush=True)
(D/'outputs/basis.json').write_text(json.dumps(r,indent=2)+'\n')
