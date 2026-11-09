import resource,os,time,json
from fractions import Fraction as F
resource.setrlimit(resource.RLIMIT_CPU,(110,110));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);start=time.time();out=[]
for r in range(2,21):
 A=[1];B=[1]
 for n in range(1,61):
  A=[(r*k+1)*(A[k]if k<len(A)else 0)+r*(n-k)*(A[k-1]if k else 0) for k in range(n)]
  B=[r*k*(B[k]if k<len(B)else 0)+(r*(n-k)+1)*(B[k-1]if k else 0)for k in range(n+1)]
  P=[0]*(2*n+1)
  for k,a in enumerate(A):P[2*k+1]+=a
  for k,b in enumerate(B):P[2*k]+=b
  T=[P[0]]
  for k in range(1,len(P)):T.append(P[k]-T[-1])
  while T and T[-1]==0:T.pop()
  zeros=0
  while T and T[0]==0:T.pop(0);zeros+=1
  co=list(map(F,T[::-1]));d=len(co)-1;w=(d+2)//2
  a=co[::2]+[F(0)]*w;b=co[1::2]+[F(0)]*w;a=a[:w];b=b[:w];positive=a[0]>0 and b[0]>0;exception=None
  for i in range(2,d+1):
   if not b[0]:exception='zero pivot';break
   c=[(b[0]*a[j+1]-a[0]*b[j+1])/b[0]for j in range(w-1)]+[F(0)]
   if c[0]<=0:positive=False
   a,b=b,c
  out.append({'r':r,'n':n,'zero_roots':zeros,'routh_strict_after_zero_removal':positive,'exception':exception})
  json.dump({'coverage':out,'seconds':time.time()-start},open('outputs/peak-exact.json','w'),indent=2)
  if time.time()-start>100:print('time cap');raise SystemExit
print('completed',len(out))
