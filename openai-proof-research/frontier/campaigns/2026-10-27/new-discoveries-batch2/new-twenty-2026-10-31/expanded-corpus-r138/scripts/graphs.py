import itertools,json,pathlib,functools
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(2,6):
 pairs=list(itertools.combinations(range(n),2));cc=mc=col=0;mins={}
 for mask in range(1<<len(pairs)):
  E=[e for j,e in enumerate(pairs) if mask>>j&1];adj=[set() for _ in range(n)]
  for u,v in E:adj[u].add(v);adj[v].add(u)
  def connected(S):
   if not S:return False
   seen={next(iter(S))}
   while True:
    z=seen|set().union(*(adj[v]&S for v in seen))
    if z==seen:return z==S
    seen=z
  V=set(range(n))
  # Connected graphic matroid, rank n-1; for n<=5 its degree bound <=1.
  if n>=3 and all(connected(V-{v}) for v in V):
   mc+=1;r=n-1
   if r>=3:
    flats=sum(connected({v for v in V if S>>v&1}) and connected({v for v in V if not S>>v&1}) for S in range(1,1<<n) if S&1)
    c1=flats-len(E);mins[r]=min(mins.get(r,10**9),c1);assert c1>0
  # Literal cycle-double-cover extension, exhaustive cycles and exact residual recursion.
  if connected(V) and all(connected(V) for _ in [0]):
   ix={e:j for j,e in enumerate(E)};cycles=set()
   for k in range(3,n+1):
    for S in itertools.combinations(V,k):
     a=min(S)
     for p in itertools.permutations(set(S)-{a}):
      cyc=(a,)+p
      if p[0]>p[-1]:continue
      edges=[tuple(sorted((cyc[j],cyc[(j+1)%k]))) for j in range(k)]
      if all(e in ix for e in edges):cycles.add(sum(1<<ix[e] for e in edges))
   if E and all(any(c>>j&1 for c in cycles) for j in range(len(E))):
    C=sorted(cycles);by=[[c for c in C if c>>j&1] for j in range(len(E))]
    @functools.lru_cache(None)
    def solve(cap):
     if not any(cap):return True
     j=next(j for j,x in enumerate(cap) if x)
     for c in by[j]:
      if all(cap[k]>0 for k in range(len(E)) if c>>k&1):
       new=tuple(x-((c>>k)&1) for k,x in enumerate(cap))
       if solve(new):return True
     return False
    for c in C:assert solve(tuple(2-((c>>j)&1) for j in range(len(E))));cc+=1
  # Test equitable k-colouring existence; record scope covered by source theorems.
  for k in range(2,6):
   if max(map(len,adj),default=0)>k:continue
   cap=[0]*k;co=[-1]*n;equ=False;proper=False
   def color(v):
    global equ,proper
    if v==n:
     proper=True
     if max(cap)-min(cap)<=1:equ=True
     return
    for c in range(k):
     if c>0 and cap[c]==0 and cap[c-1]==0:continue
     if any(co[u]==c for u in adj[v] if u<v):continue
     co[v]=c;cap[c]+=1;color(v+1);cap[c]-=1;co[v]=-1
   color(0)
   if proper:col+=1
   if proper and not equ:
    # n<=5 source exceptional k=2 odd cycle; full strong form source assumes |G|=ks.
    print('color obstruction',n,mask,k,flush=True)
 rec=dict(n=n,labeled_graphs=1<<len(pairs),connected_graphic_matroids=mc,minimum_KL_linear_coefficient=mins,prescribed_cycle_CDC_tests=cc,color_eligible_tests=col)
 print(rec,flush=True);out.append(rec)
(D/'outputs/graphs.json').write_text(json.dumps(out,indent=2)+'\n')
