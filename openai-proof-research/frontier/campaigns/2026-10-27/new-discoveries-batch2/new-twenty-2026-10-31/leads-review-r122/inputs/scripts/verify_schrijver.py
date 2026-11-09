import itertools,json,pathlib,collections,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
rows=[]
for n,k in [(14,6),(22,10),(23,10)]:
 # Independent direct k-subset enumeration; no compressed gap formula or orbit reduction.
 V=[c for c in itertools.combinations(range(n),k) if all(c[i+1]>c[i]+1 for i in range(k-1)) and not(c[0]==0 and c[-1]==n-1)]
 S=list(map(set,V));adj=[[j for j,y in enumerate(S) if not(x&y)] for x in S];distances=[];parents=[];diam=0;pair=None
 for s in range(len(V)):
  ds=[-1]*len(V);pa=[-1]*len(V);ds[s]=0;q=collections.deque([s])
  while q:
   u=q.popleft()
   for v in adj[u]:
    if ds[v]<0:ds[v]=ds[u]+1;pa[v]=u;q.append(v)
  assert min(ds)>=0
  if max(ds)>diam:diam=max(ds);pair=[s,ds.index(diam)]
  # Distance labels certify lower bounds: every edge changes label by at most 1.
  assert all(abs(ds[u]-ds[v])<=1 for u,a in enumerate(adj) for v in a)
  # Parents certify an upper path for every vertex.
  assert all(v==s or (pa[v] in adj[v] and ds[pa[v]]+1==ds[v]) for v in range(len(V)))
  distances.append(ds);parents.append(pa)
 out={'n':n,'k':k,'vertices_zero_based':V,'adjacency':adj,'distance_rows':distances,'parent_rows':parents,'diameter':diam,'diameter_pair_indices':pair}
 p=D/f'outputs/SG-{n}-{k}-certificate.json';p.write_text(json.dumps(out,separators=(',',':'))+'\n')
 row={'n':n,'k':k,'vertices':len(V),'diameter':diam,'pair_zero_based':[V[i] for i in pair],'certificate_sha256':hashlib.sha256(p.read_bytes()).hexdigest()};rows.append(row);print(row,flush=True)
(D/'outputs/schrijver-independent.json').write_text(json.dumps(rows,indent=2))
