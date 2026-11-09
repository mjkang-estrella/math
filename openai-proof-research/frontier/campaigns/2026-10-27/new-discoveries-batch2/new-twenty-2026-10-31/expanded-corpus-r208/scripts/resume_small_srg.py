import itertools,json
# Exhaust all labelled graphs through six vertices, checking SRG lambda=1, mu=2.
for n in range(3,7):
 e=list(itertools.combinations(range(n),2));matches=0
 for bits in range(1<<len(e)):
  adj=[0]*n
  for j,(a,b) in enumerate(e):
   if bits>>j&1:adj[a]|=1<<b;adj[b]|=1<<a
  k=adj[0].bit_count()
  if k in (0,n-1) or any(a.bit_count()!=k for a in adj):continue
  if not all((adj[a]&adj[b]).bit_count()==(1 if bits>>j&1 else 2) for j,(a,b) in enumerate(e)):continue
  matches+=1
 print(json.dumps({'n':n,'labelled_graphs':1<<len(e),'nontrivial_srg_lambda1_mu2':matches}),flush=True)
# Rook graph on 3x3: induced hexagons, not arbitrary six-cycles.
n=9;adj=[{j for j in range(n) if j!=i and (i//3==j//3 or i%3==j%3)} for i in range(n)]
hexagons=[]
for S in itertools.combinations(range(n),6):
 if all(len(adj[i]&set(S))==2 for i in S):
  seen={S[0]};todo=[S[0]]
  while todo:
   for j in adj[todo.pop()]&set(S)-seen:seen.add(j);todo.append(j)
  if len(seen)==6:hexagons.append(S)
print(json.dumps({'rook9_induced_hexagons':len(hexagons),'conjectured':6,'subsets':hexagons}))
