import itertools,json
n=5;es=list(itertools.combinations(range(n),2));cols=[]
for c in itertools.product(range(3),repeat=n-1):
 c=(0,)+c
 if all(c[i]<=max(c[:i])+1 for i in range(1,n)):cols.append(c)
def acyclic(arcs):
 adj=[0]*n
 for u,v in arcs:adj[u]|=1<<v
 for k in range(n):
  for u in range(n):
   if adj[u]>>k&1:adj[u]|=adj[k]
 return all(not(adj[u]>>u&1) for u in range(n))
count=0;bad=[];by={}
for bits in itertools.product(range(3),repeat=len(es)):
 # Every underlying proper subgraph of K5 is planar. K5 orientations excluded.
 if 0 not in bits:continue
 arcs=[(u,v) if b==1 else (v,u) for (u,v),b in zip(es,bits) if b];count+=1;good=None
 for c in cols:
  if all(acyclic([(u,v) for u,v in arcs if c[u]==a and c[v]==a]) for a in range(3)) and all(acyclic([(u,v) for u,v in arcs if {c[u],c[v]}=={a,b}]) for a in range(3) for b in range(a+1,3)):
   good=max(c)+1;break
 if good is None:bad.append(arcs)
 else:by[good]=by.get(good,0)+1
print(json.dumps({'vertices':5,'labeled_planar_orientations':count,'tested_source_acyclic_dichromatic_definition':True,'colorings_by_first_found_number':by,'counterexamples':bad}))
