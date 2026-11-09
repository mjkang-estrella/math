import itertools as it,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out={'graphs':[],'eta':[],'vizing_critical':[],'strong_majority_failures':[],'fourcritical_trianglefree':[]}
def color(E,n,k,strong=False):
 m=len(E);adj=[{j for j,f in enumerate(E) if j!=i and set(e)&set(f)} for i,e in enumerate(E)];order=sorted(range(m),key=lambda e:-len(adj[e]));c=[-1]*m
 if strong:
  if any(len(s)==1 for s in adj):return None
  constraints=[[i for i in range(m) if j in adj[i]] for j in range(m)];counts=[[0]*k for _ in E]
 else:counts=None
 def go(d,hi):
  if d==m:return c.copy()
  e=order[d]
  for z in range(min(k,hi+2)):
   if strong:
    if any(2*(counts[j][z]+1)>len(adj[j]) for j in constraints[e]):continue
    for j in constraints[e]:counts[j][z]+=1
   elif any(c[j]==z for j in adj[e]):continue
   c[e]=z;r=go(d+1,max(hi,z))
   if r is not None:return r
   c[e]=-1
   if strong:
    for j in constraints[e]:counts[j][z]-=1
  return None
 return go(0,-1)
for n in range(1,6):
 pairs=list(it.combinations(range(n),2));strong_ok=0;p5free=0
 for mask in range(1<<len(pairs)):
  E=[e for i,e in enumerate(pairs) if mask>>i&1];nb=[0]*n
  for u,v in E:nb[u]|=1<<v;nb[v]|=1<<u
  deg=[s.bit_count() for s in nb];delta=max(deg);m=len(E)
  # admissibility is exactly no line graph vertex of degree one.
  admissible=all(deg[u]+deg[v]!=3 for u,v in E)
  if admissible:
   r=color(E,n,4,True)
   if r is None:out['strong_majority_failures'].append([n,mask])
   else:strong_ok+=1
  # edge-Delta-critical = class two with every edge deletion Delta-colorable, connected.
  connected={0};queue=[0]
  for v in queue:
   for w in range(n):
    if nb[v]>>w&1 and w not in connected:connected.add(w);queue.append(w)
  if len(connected)==n and E and color(E,n,delta) is None and all(color(E[:i]+E[i+1:],n,delta) is not None for i in range(m)):
   out['vizing_critical'].append({'n':n,'mask':mask,'delta':delta,'twom':2*m,'bound_ok':2*m>=n*(delta-1)+3})
  # clique/stable sets and exact max-stable-set transversal.
  stable=[s for s in range(1<<n) if all(not(nb[i]&s) for i in range(n) if s>>i&1)]
  alpha=max(map(int.bit_count,stable));maxstable=[s for s in stable if s.bit_count()==alpha]
  omega=max(s.bit_count() for s in range(1<<n) if all((nb[i]&s).bit_count()==s.bit_count()-1 for i in range(n) if s>>i&1))
  isP5=n==5 and sorted(deg)==[1,1,2,2,2] and m==4 and len(stable)<32 # connected checked below
  seen={0};q=[0]
  for v in q:
   for w in range(n):
    if nb[v]>>w&1 and w not in seen:seen.add(w);q.append(w)
  isP5=isP5 and len(seen)==5
  if not isP5:
   p5free+=1;eta=min(s.bit_count() for s in range(1<<n) if all(s&t for t in maxstable));out['eta'].append([n,mask,omega,alpha,eta])
  if all(not (nb[u]&nb[v]) for u,v in E):
   # Every triangle-free graph to order 5 is 3-colorable; explicitly enumerate.
   if not any(all(c[u]!=c[v] for u,v in E) for c in it.product(range(3),repeat=n)):out['fourcritical_trianglefree'].append([n,mask])
 out['graphs'].append({'n':n,'all_labelled_simple_graphs':1<<len(pairs),'admissible_strong4_colored':strong_ok,'P5free':p5free})
 (D/'outputs/graphs.json').write_text(json.dumps(out,indent=2))
print(out['graphs']);print('failures',out['strong_majority_failures'],out['fourcritical_trianglefree']);print('critical',out['vizing_critical'])
