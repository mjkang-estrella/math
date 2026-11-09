import itertools as it, json, pathlib, sys, time
L=pathlib.Path(__file__).resolve().parents[1]
mode=sys.argv[1]; start=time.monotonic()
if mode=='bhr':
 for n in range(2,12):
  d=n//2; seen=set();cnt=0
  for p in it.permutations(range(1,n)):
   a=(0,)+p
   if a[1]>a[-1]:continue
   hist=[0]*d
   for u,v in zip(a,a[1:]):
    k=abs(u-v);hist[min(k,n-k)-1]+=1
   seen.add(tuple(hist));cnt+=1
  good=0;missing=[]
  def comps(s,k):
   if k==1:yield(s,);return
   for a in range(s+1):
    for b in comps(s-a,k-1):yield(a,)+b
  for h in comps(n-1,d):
   if all(sum(h[i-1] for i in range(1,d+1) if i%q==0)<=n-q for q in range(1,n+1) if n%q==0):
    good+=1
    if h not in seen:missing.append(h)
  print(json.dumps(dict(n=n,paths=cnt,realized=len(seen),admissible=good,missing=missing,seconds=time.monotonic()-start)),flush=True)
elif mode=='cube':
 for n in range(3,5):
  cubes=[]
  for p in it.product('01*',repeat=n):
   bits=sum(1<<x for x in range(1<<n) if all(c=='*' or int(c)==(x>>j&1) for j,c in enumerate(p)))
   cubes.append((''.join(p),bits))
  full=(1<<(1<<n))-1;bypt=[[i for i,(_,b) in enumerate(cubes) if b>>x&1] for x in range(1<<n)]
  total=tight=irred=0; weights=set();bad=[]
  def walk(left,part):
   global total,tight,irred
   if not left:
    total+=1
    if not all(any(cubes[i][0][j]!='*' for i in part) for j in range(n)):return
    tight+=1
    # A proper cube is reducible iff the partition cells fully contained in it cover it with at least two cells.
    for _,b in cubes:
     if b==full:continue
     cells=[cubes[i][1] for i in part if cubes[i][1]&b==cubes[i][1]]
     if len(cells)>1 and sum(cells)==b:return
    irred+=1
    w=tuple(sum(cubes[i][0].count('1')==h for i in part) for h in range(n+1));weights.add(w)
    a=(1,n-1,n-1)+(0,)*(n-2);b=(1,n,n-3,1)+(0,)*(n-3)
    if not any(all(sum(w[h:])>=sum(v[h:]) for h in range(n+1)) for v in (a,b)):bad.append([cubes[i][0] for i in part])
    return
   x=(left&-left).bit_length()-1
   for i in bypt[x]:
    b=cubes[i][1]
    if b&left==b:walk(left^b,part+[i])
  walk(full,[])
  mins=[w for w in weights if not any(v!=w and all(sum(w[h:])>=sum(v[h:]) for h in range(n+1)) for v in weights)]
  print(json.dumps(dict(n=n,partitions=total,tight=tight,irreducible=irred,weight_vectors=len(weights),minimal_weights=mins,counterexamples=bad,seconds=time.monotonic()-start)),flush=True)
