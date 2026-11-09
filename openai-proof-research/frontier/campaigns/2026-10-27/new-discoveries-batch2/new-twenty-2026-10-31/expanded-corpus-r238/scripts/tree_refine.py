import pathlib,json,importlib.util,collections,itertools,time
D=pathlib.Path(__file__).resolve().parents[1]
# Import definitions without executing sweep.
ns={"__file__":str(D/"scripts/trees.py")};exec((D/'scripts/trees.py').read_text().split('level={()}')[0],ns)
graph=ns['graph'];match=ns['match'];canonical=ns['canonical']
def tuples(x):return tuple(map(tuples,x))
def coeffs(g):
 n=len(g);out=collections.Counter();counts=collections.Counter();allmask=(1<<n)-1
 # Only connected shores with independent complement survive edge IE for full-cover walks.
 for mask in range(1,1<<n):
  comp=allmask^mask
  if any((comp>>u&1) and (comp>>v&1) for u in range(n) for v in g[u] if u<v):continue
  vs=[u for u in range(n) if mask>>u&1];ix={u:i for i,u in enumerate(vs)};h=[[ix[v] for v in g[u] if v in ix] for u in vs]
  if sum(map(len,h))!=2*(len(h)-1):continue
  # Induced forest with k-1 edges is connected.
  poly=tuple(match(h)[1]);sgn=(-1)**(n-len(vs));out[poly]+=sgn
 return out
def moments(poly,n):
 # matching polynomial det(I-tA) coefficients: p[2j]=(-1)^j matching_j;
 # traces from -t Q'/Q, exact recurrence.
 q=[0]*(2*len(poly)-1)
 for j,x in enumerate(poly):q[2*j]=(-1)**j*x
 s=[0]*(n+1)
 for k in range(1,n+1):s[k]=-sum(q[i]*s[k-i] for i in range(1,min(k,len(q)-1)+1))- (k*q[k] if k<len(q) else 0)
 return s
raw=json.loads((D/'tree-survivors.json').read_text());results=[];surv=[]
for bucket in raw['canonical_rooted_codes']:
 dd=collections.defaultdict(list)
 for c in bucket:
  c=tuples(c);g=graph(c);co=coeffs(g);seq=[0]*91
  for poly,v in co.items():
   ms=moments(poly,90)
   for i in range(91):seq[i]+=v*ms[i]
  dd[tuple(seq)].append(c)
 surv.extend(v for v in dd.values() if len(v)>1)
print(json.dumps({'order':raw['n'],'input_buckets':len(raw['canonical_rooted_codes']),'full_cover_through_length90_surviving_buckets':len(surv),'survivors':surv}),flush=True)
(D/'tree-refined.json').write_text(json.dumps({'order':raw['n'],'input_buckets':len(raw['canonical_rooted_codes']),'full_cover_through_length90_surviving_buckets':len(surv),'survivors':surv},indent=2)+'\n')
