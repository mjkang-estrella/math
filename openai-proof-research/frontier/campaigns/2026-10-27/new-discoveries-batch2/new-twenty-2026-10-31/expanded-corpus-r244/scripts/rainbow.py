import itertools,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
def partitions(n):
 def rec(a):
  if len(a)==n:yield tuple(a);return
  for c in range(max(a,default=-1)+2):yield from rec(a+[c])
 yield from rec([0])
rows=[]
for n in range(2,int(sys.argv[1])+1):
 es=list(itertools.combinations(range(n),2));graphs=colorings=0
 for mask in range(1<<len(es)):
  a=[0]*n
  for i,(u,v) in enumerate(es):
   if mask>>i&1:a[u]|=1<<v;a[v]|=1<<u
  omega=1
  for s in range(1,1<<n):
   if all((a[v]&s)==(s^(1<<v)) for v in range(n) if s>>v&1):omega=max(omega,s.bit_count())
  cols=[c for c in partitions(n) if all(c[u]!=c[v] for u,v in es if a[u]>>v&1)];chi=min(max(c)+1 for c in cols);graphs+=1
  r=max(3,omega+1);target=1
  while target**(r-2)<chi:target+=1
  def exists(c):
   def walk(path,used,colors):
    if len(path)>=target:return True
    for v in range(n):
     if used>>v&1 or c[v] in colors or not(a[path[-1]]>>v&1):continue
     if any(a[u]>>v&1 for u in path[:-1]):continue
     if walk(path+[v],used|(1<<v),colors|{c[v]}):return True
    return False
   return any(walk([v],1<<v,{c[v]}) for v in range(n))
  for c in cols:
   colorings+=1
   if not exists(c):print('COUNTEREXAMPLE',n,mask,chi,r,target,c,flush=True);raise SystemExit
 row={'n':n,'labelled_graphs':graphs,'proper_color_partitions':colorings,'r':'max(3,clique_number+1) (strongest applicable r)','path_length':'vertices, as in source'};rows.append(row);print(row,flush=True)
(D/f'rainbow-results-{sys.argv[1]}.json').write_text(json.dumps(rows,indent=2))
