import resource,itertools,json,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_bipartite_matching
start=time.monotonic()
for n in [9,10]:
 for ell in [2,3,4]:
  ranks={r:[] for r in range(1,n+1)}
  for r in ranks:
   for supp in itertools.combinations(range(n),r):
    for sig in itertools.product([1,-1],repeat=r-1):
     signs=(1,)+sig
     if sum(a!=b for a,b in zip(signs,signs[1:]))>ell:continue
     v=[0]*n
     for a,b in zip(supp,signs):v[a]=b
     ranks[r].append(tuple(v))
  result=[]
  for r in range(1,n):
   lo={v:i for i,v in enumerate(ranks[r])};hi=ranks[r+1];rows=[];cols=[]
   for j,y in enumerate(hi):
    for a in range(n):
     if not y[a]:continue
     x=list(y);x[a]=0
     if next((b for b in x if b),1)<0:x=[-b for b in x]
     i=lo.get(tuple(x))
     if i is not None:rows.append(i);cols.append(j)
   g=csr_matrix(([1]*len(rows),(rows,cols)),shape=(len(lo),len(hi)));m=maximum_bipartite_matching(g);size=sum(m>=0);result.append([r,len(lo),len(hi),int(size)]);assert size==min(len(lo),len(hi))
  print(json.dumps({'n':n,'ell':ell,'adjacent_saturated_matching_sizes':result}),flush=True)
print('elapsed',time.monotonic()-start)
