import itertools,math,time,json,sys
m=int(sys.argv[1]); maxn=int(sys.argv[2]);start=time.monotonic()
for n in range(maxn,maxn+1):
 for t in range(2,n+1):
  A=[[0]*(n+1) for _ in range(n+1)]; roots=[(i,i+d) for d in range(1,n) for i in range(1,n-d+1) if i+d>t];nodes=[0]
  def rec(pos):
   if pos==len(roots):return 1
   i,j=roots[pos];low=max(A[i+1][j],A[i][j-1]);high=m
   for k in range(i+1,j):
    s=A[i][k]+A[k][j];low=max(low,min(m,s));high=min(high,s+1)
   total=0
   for v in range(low,high+1):A[i][j]=v;total+=rec(pos+1)
   A[i][j]=0
   return total
  c=rec(0);want=math.comb((m+1)*n-t,n-t)*(m*t+1)//(m*n+1)
  print(json.dumps({'n':n,'m':m,'t':t,'count':c,'formula':want,'equal':c==want,'elapsed':time.monotonic()-start}),flush=True)
  if c!=want:sys.exit(2)
