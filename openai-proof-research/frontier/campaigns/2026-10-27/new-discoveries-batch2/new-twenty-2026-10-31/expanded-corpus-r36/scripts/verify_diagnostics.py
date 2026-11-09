import json,pathlib,collections,resource
resource.setrlimit(resource.RLIMIT_AS,(1024**3,)*2);resource.setrlimit(resource.RLIMIT_CPU,(15,15))
L=pathlib.Path(__file__).resolve().parent.parent;d=json.loads((L/'code-witness.json').read_text());A=d['rows'];n=d['n']
assert all(not(A[i]>>i&1) and all((A[i]>>j&1)==(A[j]>>i&1) for j in range(n)) for i in range(n))
def image(s):
 return sum((sum((s>>j&1)*(A[j]>>i&1) for j in range(n))%2)<<i for i in range(n))
w=[s.bit_count()+image(s).bit_count() for s in range(1,1<<n)]
assert min(w)==5 and image(d['S'])==d['vonS'] and d['S']&d['vonS'] and d['S']!=d['vonS']
code={'distance':min(w),'weights':dict(sorted(collections.Counter(w).items())),'S':[i for i in range(n) if d['S']>>i&1],'vonS':[i for i in range(n) if d['vonS']>>i&1],'nonzero_messages':len(w),'status':'exact Python diagnostic, not Lean theorem'}
edges=['05','06','07','09','0X','15','17','1X','26','27','29','2X','36','38','3X','48','4X','58','59','69','79','7X','9X'];adj=[set() for _ in range(11)]
for a,b in edges:
 a=int(a,16) if a!='X' else 10;b=int(b,16) if b!='X' else 10;adj[a].add(b);adj[b].add(a)
D=[]
for v in range(11):
 dist={v:0};q=collections.deque([v])
 while q:
  u=q.popleft()
  for x in adj[u]:
   if x not in dist:dist[x]=dist[u]+1;q.append(x)
 D.append([dist[i] for i in range(11)])
def resolves(s):
 reps=[tuple(sorted(D[v][i] for i in range(11) if s>>i&1)) for v in range(11)]
 return len(set(reps))==11
passing=[s for s in range(1<<11) if resolves(s)];assert passing==[2047]
(L/'diagnostic-verification.json').write_text(json.dumps({'graph_code':code,'published_multiset_G1':{'resolving_masks':passing,'all_subsets_checked':2048,'status':'independent exact Python reproduction of public example; zero credit'}},indent=2)+'\n');print((L/'diagnostic-verification.json').read_text())
