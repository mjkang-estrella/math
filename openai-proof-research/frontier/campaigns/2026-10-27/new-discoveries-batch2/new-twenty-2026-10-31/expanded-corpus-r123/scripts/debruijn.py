from pathlib import Path
import itertools,json
D=Path(__file__).resolve().parents[1]
for m in range(1,5):
 totals={}; found=False
 for n in range(m+2,m+5):
  pairs=trees=functions=truncated=0
  for truth in range(1<<(1<<(m-1))):
   mask=(1<<n)-1
   def f(v):
    a=v&((1<<m)-1);return (a>>(m-1))^((truth>>(a&((1<<(m-1))-1)))&1)
   succ=[((v<<1)&mask)|f(v) for v in range(1<<n)]
   cycles=[];comp={}
   for v in range(1<<n):
    if v in comp:continue
    path=[];pos={};u=v
    while u not in comp and u not in pos:pos[u]=len(path);path.append(u);u=succ[u]
    if u in comp:idx=comp[u]
    else:idx=len(cycles);cycles.append(path[pos[u]:])
    for u in path:comp[u]=idx
   t=len(cycles);arcs=[(i,comp[w^1],w) for i,c in enumerate(cycles) for w in c if i!=comp[w^1]]
   seen={};functions+=1
   for root in range(t):
    other=[j for j in range(t) if j!=root];opts=[[a for a in arcs if a[0]==j] for j in other]
    num=0
    for es in itertools.product(*opts):
     parent={a:b for a,b,w in es};valid=True
     for j in other:
      visited=set();u=j
      while u!=root and u not in visited:visited.add(u);u=parent[u]
      if u!=root:valid=False;break
     if not valid:continue
     num+=1
     if num>2000:truncated+=1;break
     trees+=1
     for start in cycles[root]:
      selected={w for a,b,w in es};visited=set();v=start;bits=[]
      for step in range(1<<n):
       if v in visited:raise RuntimeError(('early repeat',m,n,truth,root))
       visited.add(v);bits.append(str(v>>(n-1)));ordinary=succ[v]
       if ordinary in selected:v=ordinary;selected.remove(ordinary)
       else:
        v=ordinary^1
        if v in visited:v=ordinary
      assert v==start and len(visited)==1<<n
      s=''.join(bits);key=min(s[i:]+s[:i] for i in range(len(s)));pair=(root,es,start)
      if key in seen and seen[key]!=pair:
       o={'m':m,'n':n,'truth':truth,'previous':seen[key],'pair':pair,'sequence':key};(D/'outputs/debruijn-witness.json').write_text(json.dumps(o,indent=2));print('COLLISION',o,flush=True);raise SystemExit()
      seen[key]=pair;pairs+=1
  totals[n]={'h_functions':functions,'trees':trees,'pairs':pairs,'roots_truncated_after_2000_trees':truncated};print(m,n,totals[n],flush=True)
 print('M DONE',m,totals,flush=True)
