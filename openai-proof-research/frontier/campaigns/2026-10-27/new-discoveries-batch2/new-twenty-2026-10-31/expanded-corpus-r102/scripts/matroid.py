import itertools,random,json,functools,time
from fractions import Fraction as F
random.seed(102)
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 return trim(c)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def rem(a,b):
 a=list(map(F,a));b=list(map(F,b))
 while len(a)>=len(b) and any(a):
  q=a[-1]/b[-1];d=len(a)-len(b)
  for i,x in enumerate(b):a[i+d]-=q*x
  trim(a)
 return a

def rr(a):
 a=trim(a[:])
 if len(a)<=2:return True
 seq=[a,[i*a[i] for i in range(1,len(a))]]
 while any(seq[-1]):
  c=[-x for x in rem(seq[-2],seq[-1])]
  if not any(c):break
  seq.append(c)
 def variation(inf):
  s=[(1 if p[-1]>0 else -1)*((-1)**(len(p)-1) if inf<0 else 1) for p in seq]
  return sum(x!=y for x,y in zip(s,s[1:]))
 return variation(-1)-variation(1)==len(a)-len(seq[-1])
def rank(v):
 piv={}
 for a in v:
  while a:
   k=a.bit_length()
   if k in piv:a^=piv[k]
   else:piv[k]=a;break
 return len(piv)
def calc(v):
 n=len(v);rk=[rank([v[i] for i in range(n) if m>>i&1]) for m in range(1<<n)]
 flats=[m for m in range(1<<n) if all(rk[m|1<<i]>rk[m] for i in range(n) if not(m>>i&1))]
 @functools.cache
 def polys(a,b):
  r=rk[b]-rk[a]
  if not r:return ([1],[1],[1],[1])
  mid=[f for f in flats if f!=a and f!=b and a&f==a and f&b==f]
  s=[0]*r+[1]
  for f in mid:s=add(s,[0]*(rk[f]-rk[a])+polys(f,b)[0])
  p=trim([(s[r-i] if r-i<len(s) else 0)-(s[i] if i<len(s) else 0) for i in range((r+1)//2)])
  z=add(p,s);q=[-x for x in p];y=[-x for x in z]
  for f in mid:
   pf,zf,_,_=polys(a,f);_,_,qf,yf=polys(f,b)
   sign=(-1)**(rk[b]-rk[f]);q=add(q,[-sign*x for x in mul(pf,qf)]);y=add(y,[-sign*x for x in mul(zf,yf)])
  q=[(-1)**r*x for x in q];y=[(-1)**r*x for x in y]
  return p,z,trim(q),trim(y)
 return polys(0,(1<<n)-1)
def lc(a):return all(x>=0 for x in a) and all(a[i]*a[i]>=a[i-1]*a[i+1] for i in range(1,len(a)-1))
start=time.monotonic();count=0;fail=[];sample=[]
for r,n,num in [(3,7,1),(4,8,100),(5,10,150),(6,11,80),(7,12,20)]:
 for it in range(num):
  v=random.sample(range(1,1<<r),n);ps=calc(v);tests=[rr(ps[0]),rr(ps[1]),lc(ps[2]),lc(ps[3])];count+=1
  if not all(tests):fail.append({'vectors':v,'polys':ps,'tests':tests})
  if it==0:sample.append({'rank_cap':r,'n':n,'vectors':v,'polys':ps})
 print(json.dumps({'rank_cap':r,'n':n,'samples':num,'cumulative':count,'failures':fail,'first_examples':sample[-1:],'seconds':time.monotonic()-start}),flush=True)
