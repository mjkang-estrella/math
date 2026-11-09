import itertools,pathlib,json,heapq,sys,functools
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);m=(7*n+2)//3-1
edges=list(itertools.combinations(range(n),2));var={e:j+1 for j,e in enumerate(edges)};nv=len(edges);nc=0
known={var[(0,v)]:v<=4 for v in range(1,n)}
f=(D/f'outputs/forest{n}-reduced.cnf').open('w+');f.write(' '*120+'\n')
def fresh():
 global nv
 nv+=1;return nv
def simplify(xs):
 z=[]
 for x in xs:
  if abs(x) in known:
   if known[abs(x)]==(x>0):return None
  else:z.append(x)
 return z
def clause(xs):
 global nc
 xs=simplify(xs)
 if xs is None:return
 f.write(' '.join(map(str,xs))+' 0\n');nc+=1
def edge(u,v):return var[tuple(sorted((u,v)))]
def atmost(xs,bound):
 prev={}
 for i,x in enumerate(xs,1):
  now={j:fresh() for j in range(1,min(i,bound+1)+1)};clause([-x,now[1]])
  for j,z in prev.items():
   if j in now:clause([-z,now[j]])
   if j+1 in now:clause([-z,-x,now[j+1]])
  prev=now
 clause([-prev[bound+1]])
# Known edge variables need unit clauses in the actual formula as well as simplification.
for x,val in known.items():f.write(f'{x if val else -x} 0\n');nc+=1
atmost(list(var.values()),m);atmost([-x for x in var.values()],len(edges)-m)
for v in range(n):
 for five in itertools.combinations([edge(v,u) for u in range(n) if u!=v],n-4):clause(five)
for R in itertools.combinations(range(n),3):
 V=sorted(set(range(n))-set(R))
 for bits in range(1<<(len(V)-1)):
  A=[V[0]]+[V[j+1] for j in range(len(V)-1) if bits>>j&1];B=sorted(set(V)-set(A))
  if B:clause([edge(u,v) for u in A for v in B])
# A tree is encoded by the positions of its edges among all pairs on k labels.
trees={0:[0],1:[0],2:[1]};pairlist={k:list(itertools.combinations(range(k),2)) for k in range(n-2)}
for k in range(3,n-2):
 ix={e:i for i,e in enumerate(pairlist[k])};ts=[]
 for word in itertools.product(range(k),repeat=k-2):
  deg=[1]*k
  for v in word:deg[v]+=1
  leaves=[i for i,d in enumerate(deg) if d==1];heapq.heapify(leaves);mask=0
  for v in word:
   u=heapq.heappop(leaves);mask|=1<<ix[tuple(sorted((u,v)))];deg[u]-=1;deg[v]-=1
   if deg[v]==1:heapq.heappush(leaves,v)
  mask|=1<<ix[tuple(sorted(leaves))];ts.append(mask)
 trees[k]=ts
@functools.lru_cache(None)
def allowed(k,required):return tuple(t for t in trees[k] if t&required==required)
for size in [1,2]:
 for S in itertools.combinations(range(n),size):
  V=sorted(set(range(n))-set(S));nei={}
  for v in V:
   if size==1:nei[v]=edge(S[0],v)
   else:
    z=fresh();es=[edge(u,v) for u in S];nei[v]=z
    if any(known.get(x)==True for x in es):known[z]=True
    elif all(known.get(x)==False for x in es):known[z]=False
    else:
     for x in es:clause([-x,z])
     clause([-z]+es)
  for k in range(len(V)):
   if k>=n-2:continue
   for N in itertools.combinations(V,k):
    Ns=set(N);prefix=simplify([-nei[v] if v in Ns else nei[v] for v in V])
    if prefix is None:continue
    pairs=pairlist[k];ev=[edge(N[i],N[j]) for i,j in pairs]
    required=sum(1<<j for j,x in enumerate(ev) if known.get(x)==True)
    for T in allowed(k,required):
     clause(prefix+[x for j,x in enumerate(ev) if not T>>j&1])
 print('size',size,'clauses',nc,'vars',nv,flush=True)
f.seek(0);f.write(f'p cnf {nv} {nc}'.ljust(120)+'\n');f.close()
(D/f'outputs/forest{n}-reduced-meta.json').write_text(json.dumps(dict(n=n,m=m,variables=nv,clauses=nc,spanning_tree_counts={k:len(v) for k,v in trees.items()},symmetry='degree4 vertex0 with neighbors1,2,3,4; valid since 2m/n<5',known_edge_variables={str(x):b for x,b in known.items() if x<=len(edges)}),indent=2)+'\n')
print('DONE',nv,nc)
