import itertools,random,json
R=random.Random(203)
for r,s,n in [(3,3,7),(3,3,8),(4,2,7),(4,3,7),(4,3,8),(4,3,9)]:
 E=[sum(1<<v for v in x) for x in itertools.combinations(range(n),r)];tests=[]
 # phi<=s iff no dominating set of size n-s-1 (monotone property).
 for S in itertools.combinations(range(n),n-s-1):
  D=sum(1<<v for v in S);tests.append([sum(1<<j for j,e in enumerate(E) if e>>v&1 and (e^(1<<v))&D==(e^(1<<v))) for v in range(n) if not D>>v&1])
 best=0
 for rep in range(500):
  order=list(range(len(E)));R.shuffle(order);H=0
  for j in order:
   K=H|1<<j
   if all(not all(t&K for t in ts) for ts in tests):H=K
  size=H.bit_count()
  if size>best:best=size;print(json.dumps({'r':r,'s':s,'n':n,'rep':rep,'new_best':best,'edges':[e for j,e in enumerate(E) if H>>j&1]}),flush=True)
 print(json.dumps({'completed':[r,s,n],'trials':500,'best':best,'scope':'random greedy maximal families, not exhaustive'}),flush=True)
