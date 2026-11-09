import os,resource,json,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
r=Path(__file__).resolve().parents[1]
def rem(a,b):
 while a.bit_length()>=b.bit_length():a^=b<<(a.bit_length()-b.bit_length())
 return a
def gcd(a,b):
 while b:a,b=b,rem(a,b)
 return a
def square(a):
 out=0
 while a:
  t=a&-a;out^=1<<(2*(t.bit_length()-1));a^=t
 return out
def mul(a,b):
 c=0
 while b:
  if b&1:c^=a
  a<<=1;b>>=1
 return c
def fib(n):
 a,b=0,1
 for _ in range(n):a,b=b,(b<<1)^a
 return a
def translate(p):
 # Horner in powers of 2: splitting p=even(X²)+X odd(X²)
 if p<2:return p
 even=odd=0;pos=0
 while p:
  even|=(p&1)<<pos;odd|=((p>>1)&1)<<pos;p>>=2;pos+=1
 a,b=square(translate(even)),square(translate(odd))
 return a^b^(b<<1)
def rank(rows):
 piv={}
 for a in rows:
  while a:
   j=a.bit_length()-1
   if j in piv:a^=piv[j]
   else:piv[j]=a;break
 return len(piv)
def grid(n):
 rows=[]
 for i in range(n):
  for j in range(n):
   a=1<<(n*i+j)
   for u,v in [(i-1,j),(i+1,j),(i,j-1),(i,j+1)]:
    if 0<=u<n and 0<=v<n:a^=1<<(n*u+v)
   rows.append(a)
 return n*n-rank(rows)
res={'polynomial':[],'grid':[],'irreducibility':[],'generic_kernel_checks':[]}
start=time.monotonic()
for k in range(1,10):
 m=2*3**k;p=fib(m);q=translate(p);g=gcd(p,q);assert g==6
 # independently form factors via P_j=1+X f_(3^(j-1))
 prod=2
 for j in range(1,k+1):prod=mul(prod,square(square(1^(fib(3**(j-1))<<1))))
 assert prod==p
 res['polynomial'].append({'k':k,'n':m-1,'degree_f':p.bit_length()-1,'gcd_bits':g,'gcd':'X^2+X'})
for j in range(1,8):
 d=3**(j-1);p=1^(fib(d)<<1);x=2;a=x
 for t in range(1,d+1):
  a=rem(square(a),p)
  if d%t==0 and t<d:assert gcd(a^x,p)==1
 assert a==rem(x,p)
 assert p.bit_length()-1==d and translate(p)!=p
 res['irreducibility'].append({'j':j,'degree':d,'rabin_irreducible':True,'next_coefficient':(p>>(d-1))&1})
for k in range(4):
 n=2*3**k-1;d=grid(n);assert d==(0 if k==0 else 2)
 res['grid'].append({'k':k,'n':n,'matrix_size':n*n,'nullity':d})
# brute-force cyclic quotient kernel check, all monic f of degree <=5, all h below that degree
for d in range(1,6):
 cases=0
 for f in range(1<<d,1<<(d+1)):
  for h in range(1<<d):
   z=sum(rem(mul(h,p),f)==0 for p in range(1<<d));assert z==1<<(gcd(f,h).bit_length()-1);cases+=1
 res['generic_kernel_checks'].append({'degree':d,'cases':cases})
res['seconds']=time.monotonic()-start
(r/'logs/computations.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
