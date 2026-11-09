import pathlib,itertools,json,time
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
for n in range(3,6):
 edges=list(itertools.combinations(range(n),2));cases=0;graphs=0;bad=[]
 for mask in range(1<<len(edges)):
  A=[0]*n
  for e,(a,b) in enumerate(edges):
   if mask>>e&1:A[a]|=1<<b;A[b]|=1<<a
  # chordal by recursive simplicial elimination
  W=(1<<n)-1
  while W:
   for v in range(n):
    if not(W>>v&1):continue
    N=A[v]&W
    if all((N&~(1<<u)&~A[u])==0 for u in range(n) if N>>u&1):W^=1<<v;break
   else:break
  if W:continue
  graphs+=1
  cliques=[s for s in range(1<<n) if all((s&~(1<<u)&~A[u])==0 for u in range(n) if s>>u&1)]
  for rank in range(2,n+1):
   # uniform rank matroid, precisely computable subclass
   for m in range(1,rank+1):
    for k in range(m,min(m+1,rank)+1):
     if m+1>n:continue
     cases+=1
     hyp=True
     for U in itertools.combinations(range(n),m+1):
      if min(len(U),rank)<k:continue
      for u in U:
       if not any(A[u]>>v&1 for v in U if v!=u):hyp=False;break
      if not hyp:break
     if hyp and not any(min(n-s.bit_count(),rank)<=k-1 for s in cliques):bad.append({'graphmask':mask,'rank':rank,'m':m,'k':k})
 rows.append({'n':n,'chordal_graphs':graphs,'uniform_matroid_cases_d1':cases,'bad':bad});print(rows[-1],flush=True)
(D/'outputs/helly.json').write_text(json.dumps(rows,indent=2))
