import itertools,json,collections,pathlib
L=pathlib.Path(__file__).resolve().parent
counts=collections.Counter()
def edge(a,b):return tuple(sorted((a,b)))
def inspect(E,n):
 counts['all_histories']+=1; N=[set() for _ in range(n)]
 for a,b in E:N[a].add(b);N[b].add(a)
 ears=[i for i in range(n) if len(N[i])==2]
 if len(ears)!=2:return
 counts['two_ear_histories']+=1
 T=[frozenset(t) for t in itertools.combinations(range(n),3) if all(edge(a,b) in E for a,b in itertools.combinations(t,2))]
 D={t:[q for q in T if t!=q and len(t&q)==2] for t in T}
 assert len(T)==n-2 and sorted(map(len,D.values())).count(1)==2 and max(map(len,D.values()))<=2
 path=[next(t for t in T if ears[0] in t)]
 while len(path)<len(T):path.append(next(t for t in D[path[-1]] if t not in path))
 assert ears[1] in path[-1]
 w={};e={j:path[j-1]&path[j] for j in range(1,len(path))}
 for j in range(2,len(T)+1):
  w[j]=next(iter(path[j-1]-path[j-2]));assert w[j] not in set().union(*path[:j-1])
 k={j:next(iter(e[j]-{w[j]})) for j in range(2,len(T))}
 switches=[j for j in range(3,len(T)) if k[j]!=k[j-1]]
 cuts={}
 for j in switches:
  R={w[i] for i in range(j-1,len(T)+1)};C={ab for ab in E if (ab[0] in R)!=(ab[1] in R)}
  h=k[j-1];x=next(iter(e[j-2]-{h}));assert C=={edge(x,w[j-1]),edge(h,w[j-1]),edge(h,w[j])}
  assert ears[0] not in R and ears[1] in R;cuts[j]=C
 selected=switches[::2];assert len(set().union(*(cuts[j] for j in selected)))==3*len(selected)
 diam=0
 for start in range(n):
  dist={start:0};Q=collections.deque([start])
  while Q:
   a=Q.popleft()
   for b in N[a]:
    if b not in dist:dist[b]=dist[a]+1;Q.append(b)
  diam=max(diam,max(dist.values()))
 assert diam<=len(switches)+2
 counts['switches_checked']+=len(switches)
 counts['n'+str(n)]+=1

def run(E,n):
 inspect(E,n)
 if n==8:return
 for a,b in sorted(E):run(E|{edge(a,n),edge(b,n)},n+1)
run({(0,1),(0,2),(1,2)},3)
(L/'checker-evidence.json').write_text(json.dumps({'PASS':True,'counts':dict(counts),'coverage':'All fixed birth-order 2-tree construction histories through n=8; repeats retained. Every unlabelled 2-tree through n=8 has a representative. No universality inference from enumeration.','electrical_bound':'Analytic flow/Cauchy-Schwarz proof in review.md; no numeric resistance inference.'},indent=2)+'\n')
print(dict(counts))
