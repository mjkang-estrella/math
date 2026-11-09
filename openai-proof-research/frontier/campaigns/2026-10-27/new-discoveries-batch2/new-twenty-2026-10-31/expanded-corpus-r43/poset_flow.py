import resource,itertools,json,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_flow
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
   a=len(lo);b=len(hi);src=a+b;sink=src+1; rr=rows+list(range(a))+[src]*0+[a+j for j in range(b)];cc=[a+j for j in cols]+[sink]*0+[]
   # source-to-left, left-to-right, right-to-sink balanced integer capacities
   rr=[src]*a+rows+[a+j for j in range(b)];cc=list(range(a))+[a+j for j in cols]+[sink]*b;cap=[b]*a+[a*b]*len(rows)+[a]*b
   g=csr_matrix((cap,(rr,cc)),shape=(sink+1,sink+1));flow=maximum_flow(g,src,sink).flow_value;result.append([r,a,b,int(flow),a*b]);assert flow==a*b
  print(json.dumps({'n':n,'ell':ell,'balanced_flow' :result}),flush=True)
print('elapsed',time.monotonic()-start)
