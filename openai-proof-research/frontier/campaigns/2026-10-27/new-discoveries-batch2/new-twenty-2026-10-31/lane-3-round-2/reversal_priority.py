import itertools,random,json
rng=random.Random(321903);n=12;chains=[list(range(0,4)),list(range(4,8)),list(range(8,12))];chainof={x:i for i,C in enumerate(chains) for x in C}
def closure(edges):
 r=[[False]*n for _ in range(n)]
 for a,b in edges:r[a][b]=True
 for k in range(n):
  for i in range(n):
   if r[i][k]:
    for j in range(n):r[i][j]|=r[k][j]
 return r
def order(r,priority):
 out=[];remaining=set(range(n));rank={c:i for i,c in enumerate(priority)}
 while remaining:
  x=min((x for x in remaining if not any(r[y][x] for y in remaining)),key=lambda x:(rank[chainof[x]],x))
  out.append(x);remaining.remove(x)
 return out
def mask(L,inc):
 pos={x:i for i,x in enumerate(L)};return sum((pos[a]<pos[b])<<i for i,(a,b) in enumerate(inc))
for trial in range(20000):
 # shuffled merge of chains supplies an ambient topological order
 queues=[C.copy() for C in chains];ambient=[]
 while any(queues):
  c=rng.choice([i for i,C in enumerate(queues) if C]);ambient.append(queues[c].pop(0))
 edges=[(C[i],C[i+1]) for C in chains for i in range(3)]
 edges += [(ambient[i],ambient[j]) for i in range(n) for j in range(i+1,n) if rng.random()<.14]
 r=closure(edges);inc=[(a,b) for a in range(n) for b in range(a+1,n) if not r[a][b] and not r[b][a]]
 if not inc:continue
 orders=[order(r,p) for p in itertools.permutations(range(3))];masks=[mask(L,inc) for L in orders];diam=max((a^b).bit_count() for a in masks for b in masks)
 if 4*diam<3*len(inc):
  # Enumerate every extension to check whether this is merely a strategy obstruction.
  allorders=[]
  def rec(L,remaining):
   if not remaining:allorders.append(L);return
   for x in remaining:
    if not any(r[y][x] for y in remaining):rec(L+[x],remaining-{x})
  rec([],set(range(n)));mm=[mask(L,inc) for L in allorders];best=(-1,None)
  for i,a in enumerate(mm):
   for j,b in enumerate(mm[:i]):
    d=(a^b).bit_count()
    if d>best[0]:best=d,[i,j]
  print(json.dumps(dict(trial=trial,chains=chains,relations=[[a,b] for a in range(n) for b in range(n) if r[a][b]],incomparables=inc,priority_orders=orders,priority_diameter=diam,inc=len(inc),all_extension_count=len(mm),actual_diameter=best[0],diametral_pair=[allorders[i] for i in best[1]]),indent=2));break
else:print(json.dumps(dict(trials=20000,obstruction_found=False)))
