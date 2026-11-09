import pathlib,itertools as it,math,json,collections,sys
D=pathlib.Path(__file__).resolve().parents[1]
if sys.argv[1]=='golay':
 g=0xAE3;cols=[];x=1
 for i in range(23):
  cols.append(x);x<<=1
  if x>>11:x^=g
 syndromes={};collision=None
 for k in range(4):
  for sub in it.combinations(range(23),k):
   s=0
   for i in sub:s^=cols[i]
   if s in syndromes:collision=[sub,syndromes[s]]
   syndromes[s]=sub
 out={'mechanism':'classical binary Golay syndrome map, NOT a new construction','generator_polynomial_hex':hex(g),'columns':cols,'subset_sizes':[0,1,2,3],'subsets':sum(math.comb(23,k) for k in range(4)),'unique_syndromes':len(syndromes),'collision':collision,'group':'C2^11','m':23,'s':3,'credit':0}
 print(out);(D/'outputs/golay.json').write_text(json.dumps(out,indent=2))
if sys.argv[1]=='inversion':
 tables={};out=[]
 for n in range(1,7):
  pairs=list(it.combinations(range(n),2));index={p:i for i,p in enumerate(pairs)};dist=[-1]*(1<<len(pairs));q=collections.deque()
  for perm in it.permutations(range(n)):
   pos={v:i for i,v in enumerate(perm)};a=sum(1<<k for k,(u,v) in enumerate(pairs) if pos[u]>pos[v])
   if dist[a]<0:dist[a]=0;q.append(a)
  moves=set(sum(1<<k for k,(u,v) in enumerate(pairs) if mask>>u&1 and mask>>v&1) for mask in range(1<<n));moves.discard(0)
  while q:
   a=q.popleft()
   for move in moves:
    b=a^move
    if dist[b]<0:dist[b]=dist[a]+1;q.append(b)
  bad=[]
  if n>1:
   for a,d in enumerate(dist):
    vals=[]
    for rem in range(n):
     v=[i for i in range(n) if i!=rem];sub=sum(((a>>index[(v[i],v[j])])&1)<<k for k,(i,j) in enumerate(it.combinations(range(n-1),2)))
     vals.append(tables[n-1][sub])
    if max(vals)<d-1:bad.append(a)
  tables[n]=dist;r={'n':n,'all_labelled_tournaments':len(dist),'maximum_inversion':max(dist),'vertex_deletion_failures':bad};out.append(r);print(r,flush=True)
 (D/'outputs/inversion.json').write_text(json.dumps(out,indent=2))
if sys.argv[1]=='spanning':
 out=[]
 for m,s in [(3,2),(3,3),(4,2)]:
  coeff=[c for c in it.product(range(-s,s+1),repeat=m) if sum(map(abs,c))<=s];N=len(coeff);count=0;hits=[]
  for A in it.combinations(range(1,N),m):
   count+=1;seen=set()
   for c in coeff:
    v=sum(a*b for a,b in zip(A,c))%N
    if v in seen:break
    seen.add(v)
   else:hits.append(A)
  r={'m':m,'s':s,'cyclic_group_order':N,'all_nonzero_m_subsets':count,'perfect_spanning_sets':hits};out.append(r);print(r,flush=True)
 (D/'outputs/spanning.json').write_text(json.dumps(out,indent=2))
