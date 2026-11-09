import sys,time,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def poly(n,m,w):
 d=[[0]*(m*n+1) for _ in range(m+1)]
 for x in range(m+1):d[x][x]=1
 for i in range(1,n):
  e=[[0]*(m*n+1) for _ in range(m+1)]
  order=range(m,-1,-1) if (w>>(i-1))&1 else range(m+1)
  # relation y <= x when bit=1, otherwise y>=x
  acc=[0]*(i*m+1)
  for y in order:
   for s in range(i*m+1):acc[s]+=d[y][s]
   e[y][y:y+i*m+1]=acc[:]
  d=e
 return [sum(v) for v in zip(*d)]
N,lo,hi=map(int,sys.argv[1:]);count=0
for n in range(1,N+1):
 done=0
 for w in range(0,1<<max(0,n-1),2):
  for m in range(lo,hi+1):
   a=poly(n,m,w);down=False
   for j in range(1,len(a)):
    if a[j]<a[j-1]:down=True
    if down and a[j]>a[j-1]:print('COUNTEREXAMPLE',n,m,w,j,a,flush=True);sys.exit(1)
   count+=1;done+=1
 print(json.dumps(dict(n=n,instances=done,cumulative=count,outcome='no dip')),flush=True)
