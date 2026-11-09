import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in [4,5]:
 E=list(itertools.combinations(range(n),2));graphs=0
 for mask in range(1<<len(E)):
  edges=[e for z,e in enumerate(E) if mask>>z&1];inc={v:[e for e in edges if e[1]==v] for v in range(n)};og={v:[e for e in edges if e[0]==v] for v in range(n)}
  if any(not inc[v] for v in range(1,n)) or any(not og[v] for v in range(n-1)):continue
  routes=[]
  def gen(p):
   if p[-1]==n-1:routes.append(tuple(p));return
   for _,w in og[p[-1]]:gen(p+[w])
  gen([0]);R=len(routes)
  opts=[list(itertools.permutations(inc[v])) for v in range(1,n-1)]+[list(itertools.permutations(og[v])) for v in range(1,n-1)]
  num=1
  for a in opts:num*=len(a)
  if num>256 or R>12:continue
  observed=[]
  for combo in itertools.product(*opts):
   ir={};orr={}
   for v in range(1,n-1):
    ir.update({e:i for i,e in enumerate(combo[v-1])});orr.update({e:i for i,e in enumerate(combo[n-2+v-1])})
   comp={};direc={}
   for i,P in enumerate(routes):
    for j,Q in enumerate(routes[:i]):
     ds=[]
     for v in set(P[1:-1])&set(Q[1:-1]):
      a=P.index(v);b=Q.index(v);x=a;y=b
      while x and y and P[x-1]==Q[y-1]:x-=1;y-=1
      si=0 if not x or not y else ir[(P[x-1],P[x])]-ir[(Q[y-1],Q[y])]
      x=a;y=b
      while x+1<len(P) and y+1<len(Q) and P[x+1]==Q[y+1]:x+=1;y+=1
      so=0 if x+1==len(P) or y+1==len(Q) else orr[(P[x],P[x+1])]-orr[(Q[y],Q[y+1])]
      if si*so<0:ds.append(-1 if si<0 else 1)
     comp[i,j]=comp[j,i]=not ds
     if ds:direc[i,j]=ds[0];direc[j,i]=-ds[0]
   cliques=[]
   for z in range(1<<R):
    S=[i for i in range(R) if z>>i&1]
    if all(comp[i,j] for i,j in itertools.combinations(S,2)) and all(any(not comp[i,j] for i in S) for j in range(R) if j not in S):cliques.append(frozenset(S))
   N=len(cliques);reach=[1<<i for i in range(N)]
   for i,C in enumerate(cliques):
    for j,F in enumerate(cliques):
     if len(C-F)==len(F-C)==1 and direc[next(iter(C-F)),next(iter(F-C))]<0:reach[i]|=1<<j
   for k in range(N):
    for i in range(N):
     if reach[i]>>k&1:reach[i]|=reach[k]
   assert all(not(reach[i]>>j&1 and reach[j]>>i&1) for i in range(N) for j in range(i))
   counts={}
   for i in range(N):
    for j in range(N):
     if not reach[i]>>j&1:continue
     interval=[x for x in range(N) if reach[i]>>x&1 and reach[x]>>j&1]
     if all(reach[x]>>y&1 or reach[y]>>x&1 for x,y in itertools.combinations(interval,2)):counts[len(interval)-1]=counts.get(len(interval)-1,0)+1
   observed.append(counts)
  row={'n':n,'edges':edges,'framings':len(observed),'routes':R,'linear_interval_counts':observed[0],'invariant':all(x==observed[0] for x in observed)};out.append(row)
  if not row['invariant']:print('POTENTIAL',row,flush=True)
  graphs+=1
  if n==5 and graphs>=24:break
 print('completed',n,graphs,flush=True)
(D/'outputs/framing.json').write_text(json.dumps(out,indent=2)+'\n')
