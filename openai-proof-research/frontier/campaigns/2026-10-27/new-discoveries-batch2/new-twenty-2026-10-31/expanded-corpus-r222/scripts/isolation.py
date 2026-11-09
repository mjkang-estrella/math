import functools,itertools,random,sys,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def check(n,edges):
 A=[0]*n
 for i,j in edges:A[i]|=1<<j;A[j]|=1<<i
 C=[a|1<<i for i,a in enumerate(A)]
 @functools.lru_cache(None)
 def f(R):
  active=sum(1<<i for i in range(n) if R>>i&1 and A[i]&R)
  if not active:return (0,0)
  q=[f(R&~c) for c in C if c&active]
  return (1+min(a[1] for a in q),1+max(a[0] for a in q))
 return f((1<<n)-1)
def connected(n,edges):
 a=[set() for i in range(n)]
 for i,j in edges:a[i].add(j);a[j].add(i)
 seen={0};old=set()
 while seen!=old:old=seen.copy();seen.update(*(a[i] for i in old))
 return len(seen)==n
rng=random.Random(222)
for n in range(7,8) if sys.argv[1]=='all' else range(7,25):
 count=0;mx=[0,0];hist={};total=(1<<(n*(n-1)//2)) if sys.argv[1]=='all' else 2000
 for z in range(total):
  if sys.argv[1]=='all':
   E=[e for k,e in enumerate(itertools.combinations(range(n),2)) if z>>k&1]
   if not connected(n,E):continue
  else:
   E=[(rng.randrange(i),i) for i in range(1,n)]
   if z%2:E=list(set(E)|{e for e in itertools.combinations(range(n),2) if rng.random()<.12})
  q=check(n,E);count+=1;mx=[max(mx[i],q[i]) for i in [0,1]];hist[str(q)]=hist.get(str(q),0)+1
  if max(q)>(3*n+6)//7:
   print('VIOLATION',n,E,q,flush=True);sys.exit()
 print(json.dumps({'n':n,'count':count,'max':mx,'histogram':hist,'mode':sys.argv[1]}),flush=True)
