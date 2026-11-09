import pathlib,itertools,math,json,random,sys
D=pathlib.Path(__file__).resolve().parents[1];random.seed(105)
mode=sys.argv[1]
if mode=='colour':
 counts={};bad=[]
 for n,r in [(4,3),(5,3),(4,4)]:
  E=list(itertools.combinations(range(n),2));count=0;mn=100000
  # quotient by permutations of colours: restricted growth sequences
  def go(a,m):
   if len(a)==len(E):yield a;return
   for c in range(min(r-1,m+1)+1):yield from go(a+[c],max(m,c))
  for a in go([], -1):
   best=0
   for c in range(r):
    par=list(range(n))
    def root(x):
     while par[x]!=x:x=par[x]
     return x
    for e,z in zip(E,a):
     if z==c:par[root(e[0])]=root(e[1])
    ct={}
    for e,z in zip(E,a):
     if z==c:k=root(e[0]);ct[k]=ct.get(k,0)+1
    best=max([best]+list(ct.values()))
   mn=min(mn,best);count+=1
  counts[f'{n},{r}']=dict(colour_orbits=count,min_largest_edges=mn,bound=math.ceil(len(E)/(r*(r-1))))
 (D/'outputs/colour.json').write_text(json.dumps(counts,indent=2));print(counts)
elif mode=='digraph':
 out=[]
 for n in range(3,6):
  pairs=list(itertools.combinations(range(n),2));best={k:0 for k in range(2,n)};ct=0
  for states in itertools.product(range(3),repeat=len(pairs)):
   adj=[[] for _ in range(n)];m=0
   for (u,v),s in zip(pairs,states):
    if s:adj[u if s==1 else v].append(v if s==1 else u);m+=1
   if not all(adj):continue
   strong=True
   for s in range(n):
    seen={s};q=[s]
    for u in q:
     for v in adj[u]:
      if v not in seen:seen.add(v);q.append(v)
    if len(seen)<n:strong=False;break
   if not strong:continue
   ct+=1
   for k in best:
    valid=True
    for s in range(n):
     counts=[0]*n;counts[s]=1;front=[s]
     for _ in range(k):
      nex=[]
      for u in front:
       for v in adj[u]:counts[v]+=1;nex.append(v)
      if max(counts)>1:valid=False;break
      front=nex
     if not valid:break
    if valid:best[k]=max(best[k],m)
  z=dict(n=n,strong_oriented_graphs=ct,max_arcs=best);out.append(z);print(z,flush=True)
 (D/'outputs/digraph.json').write_text(json.dumps(out,indent=2))
elif mode=='goldbach':
 out=[]
 for n in list(range(4,101))+[200,500,1000]:
  prime=bytearray(b'\1')*(2*n+1);prime[:2]=b'\0\0'
  for p in range(2,math.isqrt(2*n)+1):
   if prime[p]:prime[p*p::p]=b'\0'*len(prime[p*p::p])
  row=[]
  for near in [False,True]:
   V=range(1,n+1) if near else range(n+1);adj={i:[] for i in V}
   def good(x):return (x%2 and prime[x]) or (near and x==1)
   for i in V:
    for j in range(i+1,n+1):
     if good(i+j) and good(j-i):adj[i].append(j);adj[j].append(i)
   diam=0
   for s in V:
    d={s:0};q=[s]
    for u in q:
     for v in adj[u]:
      if v not in d:d[v]=d[u]+1;q.append(v)
    if len(d)<len(V):diam=None;break
    diam=max(diam,max(d.values()))
   row.append(diam)
  out.append(dict(n=n,goldbach_diameter=row[0],near_diameter=row[1]));print(out[-1],flush=True)
 (D/'outputs/goldbach.json').write_text(json.dumps(out,indent=2))
