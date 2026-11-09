import itertools,random,json,pathlib,functools
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(153)
def red(A,x):
 ns=[i for i,v in enumerate(A[x]) if v]
 B=[r[:] for r in A]
 for i,j in itertools.combinations(ns,2):B[i][j]+=1;B[j][i]+=1
 return [[B[i][j] for j in range(len(A)) if j!=x] for i in range(len(A)) if i!=x]
def wyes(A):return [i for i,r in enumerate(A) if sorted(v for v in r if v)==[2,2,2]]
def tris(A):return [(i,j,k) for i,j,k in itertools.combinations(range(len(A)),3) if A[i][j] and A[i][k] and A[j][k]]
def exp(A,t):
 B=[r[:]+[0] for r in A]+[[0]*(len(A)+1)]
 for i,j in itertools.combinations(t,2):B[i][j]-=1;B[j][i]-=1
 for i in t:B[i][-1]=B[-1][i]=2
 return B
def greedy(A):
 while (W:=wyes(A)):A=red(A,rng.choice(W))
 return A
def mis(G):
 n=len(G);adj=[sum(1<<j for j in G[i]) for i in range(n)];best=[];size=0
 def rec(avail,sel):
  nonlocal size,best
  if len(sel)+avail.bit_count()<size:return
  if not avail:
   if len(sel)>size:size=len(sel);best=[sel]
   elif len(sel)==size:best.append(sel)
   return
  bit=avail&-avail;i=bit.bit_length()-1
  rec(avail^bit,sel);rec(avail&~(bit|adj[i]),sel+[i])
 rec((1<<n)-1,[]);return size,best
def random_cubic(n,seed):
 r=random.Random(seed)
 while True:
  st=list(range(n))*3;r.shuffle(st);E=[tuple(sorted(st[i:i+2])) for i in range(0,len(st),2)]
  if any(i==j for i,j in E) or len(set(E))!=len(E):continue
  G={i:set() for i in range(n)}
  for i,j in E:G[i].add(j);G[j].add(i)
  return G
def connected(G):
 seen={0};todo=[0]
 while todo:
  for j in G[todo.pop()]-seen:seen.add(j);todo.append(j)
 return len(seen)==len(G)
out=[]
for n in [12,14,16,18,20,22,24]:
 for trial in range(10):
  G=random_cubic(n,n*100+trial)
  if not connected(G):continue
  alpha,sets=mis(G);A=[[2*int(j in G[i]) for j in range(n)] for i in range(n)]
  @functools.lru_cache(None)
  def pure(T):
   A=list(map(list,T));W=wyes(A)
   if not W:return (len(A),(T,))
   results=[pure(tuple(map(tuple,red(A,x)))) for x in W]
   b=min(v[0] for v in results);states=set(t for v in results if v[0]==b for t in v[1])
   return b,tuple(sorted(states)[:20])
  base,starts=pure(tuple(map(tuple,A)));best=base;attempts=0
  for T in starts:
   B=list(map(list,T))
   for rep in range(60):
    C=B
    for depth in range(8):
     T=tris(C)
     if not T:break
     C=exp(C,rng.choice(T))
     if rng.randrange(2) and (T2:=tris(C)):C=exp(C,rng.choice(T2))
     C=greedy(C);attempts+=1
     best=min(best,len(C))
     if len(C)>base+2:break
  out.append({'n':n,'trial':trial,'graph_edges':sorted(map(sorted,[(i,j) for i in G for j in G[i] if i<j])),'alpha':alpha,'max_independent_sets':len(sets),'starting_states_used':len(starts),'pure_reduction_states':pure.cache_info().currsize,'pure_minimum_order':base,'trial_expansion_greedy_moves':attempts,'smallest_order_found':best})
 print(n,len(out),'improvements',sum(r['smallest_order_found']<r['pure_minimum_order'] for r in out),flush=True)
(L/'outputs/delta.json').write_text(json.dumps(out,indent=2))
