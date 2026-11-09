import pathlib,itertools,json,sys
D=pathlib.Path(__file__).resolve().parents[1];b=int(sys.argv[1]);n=b+3;edges=[(i,j) for i in range(3) for j in range(3,n)];ei={e:k for k,e in enumerate(edges)};adj=[[] for _ in range(n)]
for (i,j),z in ei.items():adj[i].append((j,z));adj[j].append((i,z))
clauses=[];nv=3*len(edges)
for e in range(len(edges)):
 v=[3*e+c+1 for c in range(3)];clauses.append(v)
 for a,c in itertools.combinations(v,2):clauses.append([-a,-c])
for s in range(n):
 for t in range(s+1,n):
  choices=[]
  def dfs(v,seen,path):
   global nv
   if v==t:
    for seq in ([(c,) for c in range(3)] if len(path)==1 else list(itertools.permutations(range(3)))):
     nv+=1;choices.append(nv)
     for i,e in enumerate(path):clauses.append([-nv,3*e+seq[i%len(seq)]+1])
    return
   for w,e in adj[v]:
    if not(seen>>w&1):dfs(w,seen|1<<w,path+[e])
  dfs(s,1<<s,[]);clauses.append(choices)
p=D/f'spc-K3-{b}.cnf';p.write_text(f'p cnf {nv} {len(clauses)}\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n');print(json.dumps(dict(graph=f'K3,{b}',vertices=n,edges=len(edges),variables=nv,clauses=len(clauses))))
