import itertools as it,time,json,sys
n=int(sys.argv[1]);maxcells=2*n-1;s=time.monotonic();nodes=complete=irr=0;bad=[];cut=False
# Canonicalize only coordinate permutations of the cell containing the zero vertex.
cubes=[]
for p in it.product('01*',repeat=n):
 b=sum(1<<x for x in range(1<<n) if all(c=='*' or int(c)==(x>>j&1) for j,c in enumerate(p)))
 cubes.append((''.join(p),b))
full=(1<<(1<<n))-1
bypt=[[i for i,(_,b) in enumerate(cubes) if b>>x&1] for x in range(1<<n)]
contained=[[j for j,(_,c) in enumerate(cubes) if c&b==c] for _,b in cubes]
def reducible(part):
 for _,b in cubes:
  if b==full:continue
  cs=[cubes[i][1] for i in part if cubes[i][1]&b==cubes[i][1]]
  if len(cs)>1 and sum(cs)==b:return True
 return False
def walk(left,part):
 global nodes,complete,irr,cut
 nodes+=1
 if nodes%4096==0 and time.monotonic()-s>100:cut=True;raise TimeoutError
 if not left:
  complete+=1
  if not all(any(cubes[i][0][j]!='*' for i in part) for j in range(n)):return
  if reducible(part):return
  irr+=1;w=tuple(sum(cubes[i][0].count('1')==h for i in part) for h in range(n+1))
  a=(1,n-1,n-1)+(0,)*(n-2);b=(1,n,n-3,1)+(0,)*(n-3)
  if not any(all(sum(w[h:])>=sum(v[h:]) for h in range(n+1)) for v in (a,b)):
   bad.append([cubes[i][0] for i in part]);print('FOUND',bad[-1],flush=True)
  return
 if len(part)>=maxcells:return
 x=(left&-left).bit_length()-1
 for i in bypt[x]:
  b=cubes[i][1]
  if b&left!=b:continue
  pp=part+[i]
  if len(pp)>1 and reducible(pp):continue
  walk(left^b,pp)
try:
 for k in range(1,n+1):
  root=next(i for i,(p,b) in enumerate(cubes) if p=='0'*k+'*'*(n-k))
  walk(full^cubes[root][1],[root])
  print(json.dumps(dict(n=n,zero_cell_codimension=k,nodes=nodes,complete=complete,irreducible=irr,seconds=time.monotonic()-s)),flush=True)
except TimeoutError:pass
print(json.dumps(dict(n=n,maxcells=maxcells,nodes=nodes,complete=complete,irreducible=irr,counterexamples=bad,exhaustive=not cut,seconds=time.monotonic()-s)),flush=True)
