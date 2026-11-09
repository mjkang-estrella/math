import sys,itertools,math,time,json
from fractions import Fraction as F
mode=sys.argv[1];T=time.monotonic()
if mode=='stack':
 def stack(p):
  s=[];o=[]
  for x in p:
   while s and s[-1]<x:o.append(s.pop())
   s.append(x)
  return o+s[::-1]
 for n in range(1,10):
  total=0
  for p in itertools.permutations(range(1,n+1)):
   p=list(p)+( [0]);d=0
   while p.index(0)!=0:p=stack(p);d+=1
   total+=d
  print(n,total,math.factorial(n),str(F(total,math.factorial(n))),flush=True)
elif mode=='johnson':
 def rising(x,k):return math.prod(x+j for j in range(k))
 def falling(x,k):return math.prod(x-j for j in range(k))
 for s in range(2,16):
  rare=[]
  for r in range(2,151):
   co=[F(math.comb(s,i),2**i)*falling(r+i-1,i//2)*rising(r+1,i)/rising(F(2*r+1,2),i//2) for i in range(s+1)]
   roots=[z for z in range(1,r+s) if sum(((-1)**(s-i)*falling(z,s-i)*co[i] for i in range(s+1)),F())==0]
   if len(roots)==s:rare.append([r,roots])
  print(json.dumps({'s':s,'r_min':2,'r_max':150,'all_integral_cases':rare}),flush=True)
elif mode=='partitions':
 N=10000;p=[0]*(N+1);p[0]=1
 for n in range(1,N+1):
  for j in range(1,math.isqrt(2*n)+2):
   g=j*(3*j-1)//2;h=g+j
   if g>n:break
   sign=1 if j%2 else -1;p[n]+=sign*p[n-g]
   if h<=n:p[n]+=sign*p[n-h]
 def root(x,k):
  lo=0;hi=1<<((x.bit_length()+k-1)//k)
  while lo+1<hi:
   m=(lo+hi)//2
   if m**k<=x:lo=m
   else:hi=m
  return lo
 for k in range(2,33):
  close=[]
  for n in range(2,N+1):
   a=root(p[n],k);delta=min(p[n]-a**k,(a+1)**k-p[n])
   if delta<=10:close.append([n,delta,a])
  print(json.dumps({'k':k,'n_max':N,'distance_at_most_10':close}),flush=True)
