from functools import lru_cache
import json
Q=18
@lru_cache(None)
def parts(w,n,top):
 if w==0:return ((),)
 if n==0:return ()
 return tuple((x,)+p for x in range(1,min(w,top)+1) for p in parts(w-x,n-1,x))
@lru_cache(None)
def lhs(a,b,n):
 res=[0]*(Q+1)
 for w in range(Q+1):
  for u in range(w+1):
   for p in parts(u,n,Q):
    for q in parts(w-u,n,Q):
     if all((p[j] if j<len(p) else 0)>=q[j+b] for j in range(max(0,len(q)-b))) and all((q[j] if j<len(q) else 0)>=p[j+a] for j in range(max(0,len(p)-a))):res[w]+=1
 return res
@lru_cache(None)
def qb(n,k):
 if k<0 or k>n:return (0,)*(Q+1)
 if k==0 or k==n:return (1,)+(0,)*Q
 a=qb(n-1,k);b=qb(n-1,k-1);d=n-k
 return tuple(a[j]+(b[j-d] if j>=d else 0) for j in range(Q+1))
def rhs(k,i,n,odd):
 res=[0]*(Q+1)
 for r in range(-2*n-2,2*n+3):
  ex=r*((2*k+1)*r+2*k-2*i+1)//2 if odd else r*(k*r+k-i)
  bot=(4*n-2*(2*k+1)*r+(2*k-2*i+1)*((-1)**r-1))//4 if odd else n-k*r+(k-i)*((-1)**r-1)//2
  bot=int(bot)
  if ex<0 or ex>Q:continue
  for j,x in enumerate(qb(2*n,bot)):
   if j+ex<=Q:res[j+ex]+=(-1 if r%2 else 1)*x
 for d in range(1,2*n+1):
  for j in range(d,Q+1):res[j]+=res[j-d]
 return res
for n in range(1,8):
 count=0
 for k in range(4,13):
  for i in range(1,k+1):
   for odd in [False,True]:
    a=2*k-i-(0 if odd else 1);b=i-1
    l=lhs(min(a,n),min(b,n),n);r=rhs(k,i,n,odd);count+=1
    if l!=r:print('MISMATCH',n,k,i,odd,l,r,flush=True);raise SystemExit
 print(json.dumps({'n':n,'k_min':4,'k_max':12,'all_i':True,'two_identities':True,'coefficient_degree_max':Q,'parameter_cases':count,'match':True}),flush=True)
