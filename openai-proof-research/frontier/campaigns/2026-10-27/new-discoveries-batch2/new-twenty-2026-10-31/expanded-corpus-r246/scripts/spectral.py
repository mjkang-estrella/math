import pathlib,itertools,json,time
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
def traces(adj):
 n=len(adj);q=[[int(j in adj[i])+(len(adj[i]) if i==j else 0) for j in range(n)] for i in range(n)];p=q;ts=[]
 for k in range(1,n+1):
  ts.append(sum(p[i][i] for i in range(n)))
  p=[[sum(p[i][h]*q[h][j] for h in range(n)) for j in range(n)] for i in range(n)]
 return tuple(ts)
for n in range(4,7):
 es=list(itertools.combinations(range(n),2));targets=[]
 for r in range(1,n):
  for t in range(1,n):
   if (n-r)%t:continue
   s=(n-r)//t
   if s<2 or (s==3 and t==1):continue
   adj=[set() for _ in range(n)]
   for a,b in es:
    if a<r or b<r or (a-r)//t==(b-r)//t:adj[a].add(b);adj[b].add(a)
   deg=tuple(sorted(map(len,adj)));targets.append((r,s,t,sum(deg)//2,sum(x*x for x in deg),traces(adj),deg))
 checked=0;matches=[]
 for bits in range(1<<len(es)):
  edgecount=bits.bit_count();poss=[t for t in targets if t[3]==edgecount]
  if not poss:continue
  adj=[set() for _ in range(n)]
  for k,(a,b) in enumerate(es):
   if bits>>k&1:adj[a].add(b);adj[b].add(a)
  ds=tuple(sorted(map(len,adj)));ss=sum(x*x for x in ds);poss=[t for t in poss if t[4]==ss]
  if not poss:continue
  checked+=1;ts=traces(adj)
  for r,s,t,m,z,sig,deg in poss:
   if ts==sig:
    # Same degrees plus universal r vertices and clique components detects this family.
    hubs=[v for v in range(n) if len(adj[v])==n-1];rest=set(range(n))-set(hubs);comps=[]
    while rest:
     v=next(iter(rest));todo=[v];comp=set()
     while todo:
      w=todo.pop()
      if w in comp:continue
      comp.add(w);todo.extend((adj[w]&rest)-comp)
     rest-=comp;comps.append(comp)
    iso=len(hubs)==r and len(comps)==s and all(len(c)==t and all((c-{v})<=adj[v] for v in c) for c in comps)
    if not iso:matches.append(dict(r=r,s=s,t=t,bits=bits,degrees=ds))
 row=dict(n=n,total_labeled_graphs=1<<len(es),moment_survivors=checked,target_parameters=[x[:3] for x in targets],nonisomorphic_cospectral=matches);rows.append(row);print(row,flush=True)
(D/'spectral-coverage.json').write_text(json.dumps(rows,indent=2))
