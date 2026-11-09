import itertools,json
from small_graphs import graphs,ind
# Large-MIS transversal profiles: exact exhaustive labelled census through six vertices.
for n in range(1,7):
 worst={str(c):[0,None] for c in [1,2,3,4,5,6]};count=0
 for mask,a in graphs(n):
  mis=[]
  for s in range(1,1<<n):
   if not ind(a,s):continue
   cov=s
   for v in range(n):
    if s>>v&1:cov|=a[v]
   if cov==(1<<n)-1:mis.append(s)
  for k in range(1,n+1):
   fam=[s for s in mis if s.bit_count()>=k]
   tau=next(t.bit_count() for t in sorted(range(1<<n),key=int.bit_count) if all(t&s for s in fam))
   if tau>worst[str(k)][0]:worst[str(k)]=[tau,mask]
  count+=1
 print(json.dumps(dict(kind='large_MIS',n=n,graphs=count,threshold_maxima={k:v for k,v in worst.items() if int(k)<=n})),flush=True)
# Equation 7 parameter screen, without claiming symmetric design existence.
params=[]
for l in range(3,16):
 for k in range(2,(l-1)**2):
  num=l*(l-2)*k;den=(l-1)**2-k
  if num%den:continue
  v=num//den
  if k>=v or v>200 or k*(k-1)%(v-1):continue
  params.append([v,k,l,k*(k-1)//(v-1)])
print(json.dumps(dict(kind='ULSE_integer_parameters',v_max=200,ell_max=15,parameters=params)),flush=True)
pts=list(range(16));q=lambda x:((x&1)*((x>>1)&1))^(((x>>2)&1)*((x>>3)&1))
blocks=[[x for x in pts if q(x^a)] for a in pts];colors=[(x&1)|((x>>1)&2) for x in pts]
assert all(len(b)==6 for b in blocks)
assert all(sum(u in b and v in b for b in blocks)==2 for u,v in itertools.combinations(pts,2))
assert all(sorted(sum(colors[x]==c for x in b) for c in range(4))==[0,2,2,2] for b in blocks)
print(json.dumps(dict(kind='ULSE_16_6_2',blocks=blocks,colors=colors,verified=True)),flush=True)
