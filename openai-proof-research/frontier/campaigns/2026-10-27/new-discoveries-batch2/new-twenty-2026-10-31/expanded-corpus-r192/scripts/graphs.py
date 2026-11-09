import pathlib,itertools,json,collections
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
for n in range(3,5):
 arcs=[(i,j) for i in range(n) for j in range(n) if i!=j];qualified=0;strong=0;fail=[]
 for mask in range(1<<len(arcs)):
  adj=[set() for _ in range(n)]
  for k,(u,v) in enumerate(arcs):
   if mask>>k&1:adj[u].add(v)
  def reach(s):
   seen={s};q=[s]
   for u in q:
    for v in adj[u]-seen:seen.add(v);q.append(v)
   return len(seen)==n
  if not all(reach(s) for s in range(n)):continue
  strong+=1;out=sorted(map(len,adj));inn=sorted(sum(i in adj[j] for j in range(n)) for i in range(n))
  if not all((out[i-1]>=i+1 or inn[n-i-1]>=n-i) and (inn[i-1]>=i+1 or out[n-i-1]>=n-i) for i in range(1,(n+1)//2)):continue
  qualified+=1
  if not any(all(p[(j+1)%n] in adj[p[j]] for j in range(n)) for p in ((0,)+q for q in itertools.permutations(range(1,n)))):fail.append(mask)
 rows.append({'n':n,'digraphs':1<<len(arcs),'strong':strong,'degree_hypothesis':qualified,'failures':fail})
# Published LSS obstruction B4: verify complement is (8-4)-connected.
adj=[{j for j in range(8) if j!=i and not ((i<4)!=(j<4) and i%4!=j%4)} for i in range(8)]
for k in range(4):
 for X in itertools.combinations(range(8),k):
  V=set(range(8))-set(X);seen={min(V)};q=list(seen)
  for u in q:
   for v in (adj[u]&V)-seen:seen.add(v);q.append(v)
  assert seen==V
(D/'outputs/graphs-small.json').write_text(json.dumps({'nash_williams':rows,'LSS_B4_complement':'4-connectivity verified by deleting all subsets of cardinality at most 3; nonprimality is published Conca-Welker Proposition 2.8, not recomputed'},indent=2));print(json.dumps(rows))
