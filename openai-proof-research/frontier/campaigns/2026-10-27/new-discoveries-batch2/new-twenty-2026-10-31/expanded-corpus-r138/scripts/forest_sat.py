import itertools,pathlib,json,heapq,time
D=pathlib.Path(__file__).resolve().parents[1];n=9;edges=list(itertools.combinations(range(n),2));var={e:j+1 for j,e in enumerate(edges)};nv=len(edges);nc=0
f=(D/'outputs/forest9.body.cnf').open('w')
def fresh():
 global nv
 nv+=1;return nv
def clause(xs):
 global nc
 f.write(' '.join(map(str,xs))+' 0\n');nc+=1
def edge(u,v):return var[tuple(sorted((u,v)))]
def atmost(xs,bound):
 # s[i,j] means first i inputs have >=j true literals, forward implications suffice.
 prev={}
 for i,x in enumerate(xs,1):
  now={j:fresh() for j in range(1,min(i,bound+1)+1)}
  clause([-x,now[1]])
  for j,z in prev.items():
   if j in now:clause([-z,now[j]])
   if j+1 in now:clause([-z,-x,now[j+1]])
  prev=now
 clause([-prev[bound+1]])
atmost(list(var.values()),20);atmost([-x for x in var.values()],16)
# Every counterexample at order9, size20 has a degree4 vertex; relabel it to0.
for v in range(1,n):clause([edge(0,v) if v<=4 else -edge(0,v)])
for v in range(n):
 for five in itertools.combinations([edge(v,u) for u in range(n) if u!=v],5):clause(five)
# Deletion of any three vertices leaves a connected six-vertex graph.
for R in itertools.combinations(range(n),3):
 V=sorted(set(range(n))-set(R))
 for bits in range(1<<(len(V)-1)):
  A=[V[0]]+[V[j+1] for j in range(len(V)-1) if bits>>j&1];B=sorted(set(V)-set(A))
  if B:clause([edge(u,v) for u in A for v in B])
# Generate all labelled spanning trees, once per cardinality, via Prufer codes.
trees={0:[set()],1:[set()],2:[{(0,1)}]}
for k in range(3,7):
 trees[k]=[]
 for word in itertools.product(range(k),repeat=k-2):
  deg=[1]*k
  for v in word:deg[v]+=1
  leaves=[i for i,d in enumerate(deg) if d==1];heapq.heapify(leaves);T=set()
  for v in word:
   u=heapq.heappop(leaves);T.add(tuple(sorted((u,v))));deg[u]-=1;deg[v]-=1
   if deg[v]==1:heapq.heappush(leaves,v)
  T.add(tuple(sorted(leaves)));trees[k].append(T)
for size in [1,2]:
 for S in itertools.combinations(range(n),size):
  V=sorted(set(range(n))-set(S));nei={}
  for v in V:
   if size==1:nei[v]=edge(S[0],v)
   else:
    z=fresh();es=[edge(u,v) for u in S];nei[v]=z
    for x in es:clause([-x,z])
    clause([-z]+es)
  for k in range(len(V)):
   # At n9, min degree4 guarantees a cycle if the external neighborhood has >=7 vertices.
   if k>=7:continue
   for N in itertools.combinations(V,k):
    Nset=set(N);prefix=[-nei[v] if v in Nset else nei[v] for v in V]
    for T in trees[k]:
     rest=[edge(N[i],N[j]) for i in range(k) for j in range(i+1,k) if (i,j) not in T]
     clause(prefix+rest)
 print('size',size,'clauses',nc,'vars',nv,flush=True)
f.close()
with (D/'outputs/forest9.cnf').open('wb') as g:
 g.write(f'p cnf {nv} {nc}\n'.encode())
 with (D/'outputs/forest9.body.cnf').open('rb') as h:
  while b:=h.read(1024*1024):g.write(b)
(D/'outputs/forest9-sat-meta.json').write_text(json.dumps(dict(n=n,m=20,variables=nv,clauses=nc,edge_variables={str(k):v for k,v in var.items()},scope='all labelled n9 m20 graphs with minimum degree4, 4-connectivity and 2-cyclicity, modulo choosing a degree4 vertex0 with neighbors1..4'),indent=2)+'\n')
print('DONE',nv,nc)
