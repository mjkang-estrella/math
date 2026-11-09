import pathlib,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];reg=[]
for n in range(2,7):
 E=list(itertools.combinations(range(n),2));count=0;exceptions={}
 for mask in range(1<<len(E)):
  A=[0]*n
  for j,(u,v) in enumerate(E):
   if mask>>j&1:A[u]|=1<<v;A[v]|=1<<u
  deg=[a.bit_count() for a in A]
  if len(set(deg))!=1:continue
  d=deg[0];count+=1;ok=False
  for S in range(1,(1<<n)-1):
   if all(2*(A[v]&(S if S>>v&1 else ((1<<n)-1)^S)).bit_count()>=d for v in range(n)):ok=True;break
  if not ok:exceptions[d]=exceptions.get(d,0)+1
 reg.append({'n':n,'labeled_regular_graphs':count,'no_internal_partition_counts_by_degree':exceptions})
print(reg);(D/'outputs/internal-partition.json').write_text(json.dumps(reg,indent=2))
# Signed simple graphs: ternary edge states absent/positive/negative; no claim of L* membership.
rows=[]
for n in range(2,5):
 E=list(itertools.combinations(range(n),2));critical={}
 for states in itertools.product(range(3),repeat=len(E)):
  edges=[(u,v,s-1) for (u,v),s in zip(E,states) if s]
  if not edges:continue
  values=[sum(s^((S>>u&1)^(S>>v&1)) for u,v,s in edges) for S in range(1<<(n-1))];k=min(values)
  if not k:continue
  # Removing edge reduces k iff some minimizing switch leaves that edge negative.
  if all(any(z==k and (s^((S>>u&1)^(S>>v&1))) for S,z in enumerate(values)) for u,v,s in edges):critical[k]=critical.get(k,0)+1
 rows.append({'n':n,'signed_graphs_including_empty':3**len(E),'critically_k_frustrated_counts':critical})
print(rows);(D/'outputs/signed-frustration.json').write_text(json.dumps(rows,indent=2))
