import itertools,json

def feasible(t,a,b,c):
 masks=sorted([m for m in range(1,1<<t) if m.bit_count()>=2],key=lambda m:-m.bit_count());verts=[[i for i in range(t) if m>>i&1] for m in masks];pairs=list(itertools.combinations(range(t),2));inc=[[j for j,(x,y) in enumerate(pairs) if m>>x&1 and m>>y&1] for m in masks];deg=[a]*t;cap=[c]*len(pairs);xs=[0]*len(masks);nodes=0
 def rec(k,room):
  nonlocal nodes
  nodes+=1
  if nodes>100000:raise TimeoutError
  if room<max(deg):return None
  if k==len(masks):return xs.copy() if sum(deg)<=room else None
  if sum(deg)>room*len(verts[k]):return None
  vv=verts[k];pp=inc[k];bound=min([room]+[deg[i] for i in vv]+[cap[j] for j in pp])
  for x in range(bound,-1,-1):
   for i in vv:deg[i]-=x
   for j in pp:cap[j]-=x
   xs[k]=x;z=rec(k+1,room-x)
   for i in vv:deg[i]+=x
   for j in pp:cap[j]+=x
   if z is not None:return z
  return None
 try:r=rec(0,t*b-1);return ('feasible' if r is not None else 'infeasible'),nodes
 except TimeoutError:return 'node_cap',nodes
for n in [4,5]:
 for b in range(1,7 if n==4 else 4):
  for a in range(2*b,(n-1)*b):
   p=a//b;u=(2*p*a-p*(p+1)*b+n-2)//(n-1)
   for c in sorted(set([max(0,u-1),u,u+1])):
    rows=[(t,*feasible(t,a,b,c)) for t in range(2,n+1)]
    print(json.dumps({'n':n,'a':a,'b':b,'c':c,'conjectured_options':[u-1,u],'Hall_subset_feasibility':rows}),flush=True)
