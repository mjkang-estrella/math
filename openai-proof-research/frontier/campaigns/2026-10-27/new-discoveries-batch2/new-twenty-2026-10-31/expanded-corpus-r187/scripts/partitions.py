import pathlib,json,random,itertools
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(187);hits=[];cases=0
# Petersen graph with its outer/inner cycle and spokes; girth five.
edges=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)]
for trial in range(2000):
 adj=[[0]*10 for _ in range(10)]
 for u,v in edges:adj[u][v]=adj[v][u]=rng.randint(1,5)
 deg=list(map(sum,adj));w=list(map(max,adj));budget=[deg[v]-2*w[v]+3 for v in range(10)]
 if min(budget)<4:continue
 a=[rng.randint(2,z-2) for z in budget];b=[z-x for z,x in zip(budget,a)];cases+=1
 ok=False
 for mask in range(1,1023):
  if all(sum(adj[v][u] for u in range(10) if (mask>>v&1)==(mask>>u&1))>=(a[v] if mask>>v&1 else b[v]) for v in range(10)):ok=True;break
 if not ok:hits.append({'adj':adj,'a':a,'b':b});print('HIT',hits[-1],flush=True)
print('cases',cases,'hits',len(hits))
(D/'outputs/partitions.json').write_text(json.dumps({'family':'Petersen support; edge multiplicities uniform random 1..5; maximal admissible a+b','attempted':2000,'valid_cases':cases,'hits':hits},indent=2))
