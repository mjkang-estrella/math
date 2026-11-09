import itertools,json
for n in [4,5]:
 edges=list(itertools.combinations(range(n),2));graphs=assignments=0;worst=0
 for mask in range(1<<len(edges)):
  ee=[e for j,e in enumerate(edges) if mask>>j&1];seen={0}
  while True:
   more=seen|{b for a,b in ee if a in seen}|{a for a,b in ee if b in seen}
   if more==seen:break
   seen=more
  if len(seen)!=n:continue
  graphs+=1;found=False;tries=0
  for labels in itertools.product(range(4),repeat=len(ee)):
   tries+=1;sums=[[0]*n for _ in range(2)]
   for (u,v),z in zip(ee,labels):sums[z//2][u]+=1+z%2;sums[z//2][v]+=1+z%2
   if all(sums[z//2][u]!=sums[z//2][v] for (u,v),z in zip(ee,labels)):found=True;break
  assignments+=tries;worst=max(worst,tries)
  if not found:print('FAIL',n,ee,flush=True)
 print(json.dumps({'n':n,'all_labelled_connected_graphs':graphs,'label_assignments_tested':assignments,'maximum_per_graph':worst}),flush=True)
