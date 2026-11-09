import pathlib,json,itertools,random
D=pathlib.Path(__file__).resolve().parents[1]
out={}
# Exact all 16 allocations for the four-good, two-agent partition matroids.
w=[3,1,3,1]; blocks=[[(0,1),(2,3)],[(1,2),(3,0)]]
ind=lambda s,b:all(len(s&set(c))<=1 for c in b)
value=lambda s:sum(w[i] for i in s)
ef=lambda a,b:value(a)>=value(b) or any(value(a)>=value(b-{i}) for i in b)
rows=[]
for mask in range(16):
 a={i for i in range(4) if mask>>i&1}; b=set(range(4))-a
 rows.append(dict(a=sorted(a),b=sorted(b),feasible=ind(a,blocks[0]) and ind(b,blocks[1]),ef1=ef(a,b) and ef(b,a)))
out['375232']={'weights':w,'blocks':blocks,'allocations':rows,'counterexample':not any(x['feasible'] and x['ef1'] for x in rows)}
# All labelled loopless digraphs through order four. The n=4 condition is only min in/out degree >=2.
dig=[]
for n in [3,4]:
 edges=[(i,j) for i in range(n) for j in range(n) if i!=j]; eligible=bad=0
 for mask in range(1<<len(edges)):
  adj=[[False]*n for _ in range(n)]
  for k,(i,j) in enumerate(edges):adj[i][j]=bool(mask>>k&1)
  di=sorted(sum(adj[i][j] for i in range(n)) for j in range(n));do=sorted(map(sum,adj))
  if not all(di[i-1]>=i+1 and do[i-1]>=i+1 for i in range(1,n) if 2*i<n-1):continue
  if n%2 and (di[(n-1)//2]<(n+1)//2 or do[(n-1)//2]<(n+1)//2):continue
  eligible+=1
  ham=any(all(adj[p[i]][p[(i+1)%n]] for i in range(n)) for p in ((0,)+q for q in itertools.permutations(range(1,n))))
  bad+=not ham
 dig.append(dict(n=n,all_digraphs=1<<len(edges),eligible=eligible,failures=bad))
out['374477']=dig
(D/"outputs/finite.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
