import itertools,json,pathlib
b=pathlib.Path(__file__).resolve().parent;out=[]
for n in range(3,7):
 e=list(itertools.combinations(range(n),2));m=len(e);good=set();degrees={}
 for s in range(1<<m):
  d=[0]*n
  for j,(u,v) in enumerate(e):
   if s>>j&1:d[u]+=1;d[v]+=1
  if all(not(s>>j&1) or d[u]!=d[v] for j,(u,v) in enumerate(e)):good.add(s);degrees[s]=d
 for radius in [1,2,3]:
  minima=[]
  for s in good:
   absent=[j for j in range(m) if not(s>>j&1)];present=[j for j in range(m) if s>>j&1];improve=False
   for count in range(1,min(radius,len(absent))+1):
    for added in itertools.combinations(absent,count):
     t=s|sum(1<<j for j in added)
     if t in good:improve=True;break
     if count>1 and count+1<=radius and any((t^(1<<j)) in good for j in present):improve=True;break
    if improve:break
   if not improve:minima.append(s)
  s=min(minima,key=int.bit_count)
  out.append({'n':n,'m':m,'radius':radius,'local_optima':len(minima),'minimum_kept':s.bit_count(),'global_max_kept':max(x.bit_count() for x in good),'witness_edges':[uv for j,uv in enumerate(e) if s>>j&1],'degrees':degrees[s]})
(b/'exchange.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
