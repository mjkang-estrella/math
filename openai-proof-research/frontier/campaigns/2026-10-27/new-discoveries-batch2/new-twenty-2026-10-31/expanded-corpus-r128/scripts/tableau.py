import collections,sys,math
for n in range(int(sys.argv[2]) if len(sys.argv)>2 else 1,int(sys.argv[1])+1):
 # states: row counts, previous row, b11,b12,b21,b22; weighted prefix counts
 states={(0,0,0,-1,0,0,0,0):1}
 for step in range(3*n):
  nxt=collections.defaultdict(int)
  for key,c in states.items():
   shape=key[:3];prev=key[3]
   for r in range(3):
    if shape[r]>=n or (r and shape[r]>=shape[r-1]):continue
    sh=list(shape);sh[r]+=1;bs=list(key[4:])
    if prev in (0,1) and r in (0,1):bs[2*prev+r]+=1
    nxt[(*sh,r,*bs)]+=c
  states=nxt
 counts=collections.Counter()
 for key,c in states.items():counts[key[4:]]+=c
 dc=collections.Counter()
 for (x,y,z,w),c in counts.items():dc[y,z,w]+=c
 af=[(a,c,counts[(a[2],n-a[2]-a[3],a[0],n-a[0]-a[1])]) for a,c in counts.items() if counts[(a[2],n-a[2]-a[3],a[0],n-a[0]-a[1])]!=c]
 df=[(a,c,dc[(a[0],n-a[1]-a[2]-1,a[2])]) for a,c in dc.items() if dc[(a[0],n-a[1]-a[2]-1,a[2])]!=c]
 total=sum(counts.values());hook=2*math.factorial(3*n)//(math.factorial(n)*math.factorial(n+1)*math.factorial(n+2))
 assert total==hook
 print(dict(n=n,total=total,signatures=len(counts),alpha_failures=af[:2],delta_failures=df[:2]),flush=True)
