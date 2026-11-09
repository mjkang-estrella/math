import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'logs/atlas21.log').read_text());ans=[]
for o in x['unclassified_failures']:
 es=o['edges'];n=o['n'];m=len(es);good=[]
 for mask in range(1,1<<m):
  deg=[0]*n
  for j,(u,v) in enumerate(es):
   if mask>>j&1:deg[u]+=1;deg[v]+=1
  if all(deg[u]!=deg[v] for j,(u,v) in enumerate(es) if mask>>j&1):good.append(mask)
 reach={0}
 for mask in range(1,1<<m):
  if any((mask&a)==a and (mask^a) in reach for a in good):reach.add(mask)
 ans.append({**o,'locally_irregular_nonempty_edge_subsets':len(good),'any_number_decomposable':(1<<m)-1 in reach})
print(json.dumps(ans))
