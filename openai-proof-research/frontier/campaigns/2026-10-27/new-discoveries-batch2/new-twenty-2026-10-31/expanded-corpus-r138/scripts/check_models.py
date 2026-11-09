import pathlib,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in [7,8]:
 text=(D/f'logs/forest{n}-sat.log').read_text();model={int(x) for l in text.splitlines() if l.startswith('v ') for x in l.split()[1:] if int(x)>0};pairs=list(itertools.combinations(range(n),2));E=[p for j,p in enumerate(pairs,1) if j in model];a=[set() for _ in range(n)]
 for u,v in E:a[u].add(v);a[v].add(u)
 def connected(S):
  seen={min(S)}
  while True:
   new=seen|set().union(*(a[u]&S for u in seen))
   if new==seen:return seen==S
   seen=new
 V=set(range(n))
 assert len(E)==(7*n+2)//3-1
 for k in range(4):
  for R in itertools.combinations(V,k):assert connected(V-set(R))
 for k in [1,2]:
  for S in itertools.combinations(V,k):
   N=set().union(*(a[u] for u in S))-set(S)
   if N|set(S)==V:continue
   # A finite undirected forest has |E|=|V|-components.
   unseen=set(N);components=0
   while unseen:
    components+=1;seen={min(unseen)}
    while True:
     new=seen|set().union(*(a[u]&N for u in seen))
     if new==seen:break
     seen=new
    unseen-=seen
   internal=sum(v in N and u in N for u,v in E)
   assert internal>len(N)-components
 out.append(dict(n=n,m=len(E),edges=E,connectivity_checked_deletions='all subsets of size0..3',cyclicity_checked='all vertex subsets size1..2',result='PASS; known source exception below n9'))
(D/'outputs/forest-known-exceptions-check.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
