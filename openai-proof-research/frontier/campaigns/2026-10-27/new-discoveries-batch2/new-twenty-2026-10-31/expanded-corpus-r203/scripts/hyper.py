import itertools,json
for r in (3,4):
 for n in range(r,7):
  E=[sum(1<<v for v in s) for s in itertools.combinations(range(n),r)];m=len(E)
  if m>15:continue
  tests=[]
  for k in range(n+1):
   for S in itertools.combinations(range(n),k):
    D=sum(1<<v for v in S);need=[]
    for v in range(n):
     if D>>v&1:continue
     need.append(sum(1<<j for j,e in enumerate(E) if e>>v&1 and ((e^(1<<v))&D)==(e^(1<<v))))
    tests.append((k,need))
  best={};witness={}
  for h in range(1<<m):
   gamma=next(k for k,need in tests if all(x&h for x in need));phi=n-gamma;size=h.bit_count()
   if size>best.get(phi,-1):best[phi]=size;witness[phi]=[e for j,e in enumerate(E) if h>>j&1]
  print(json.dumps({'r':r,'n':n,'hypergraphs':1<<m,'max_edges_by_exact_phi':best,'witness_bitsets':witness}),flush=True)
