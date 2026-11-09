import json,time
from sympy import factorint
from pathlib import Path
out=[]
for p in [3,5,7,11]:
 d=next(i for i in range(2,p) if pow(i,(p-1)//2,p)==p-1);Q=p*p
 def mul(a,b):
  x,y=a%p,a//p;z,w=b%p,b//p
  return (x*z+d*y*w)%p+p*((x*w+y*z)%p)
 def add(a,b):return (a%p+b%p)%p+p*((a//p+b//p)%p)
 def neg(a):return (-a%p)%p+p*((- (a//p))%p)
 def power(a,n):
  r=1
  while n:
   if n&1:r=mul(r,a)
   a=mul(a,a);n//=2
  return r
 fs=list(factorint(Q-1));N=Q**p-1;rs=list(factorint(N));bad=[];tested=0
 for lam in range(1,Q):
  if any(power(lam,(Q-1)//r)==1 for r in fs):continue
  def pmul(a,b):
   c=[0]*(2*p-1)
   for i,x in enumerate(a):
    for j,y in enumerate(b):c[i+j]=add(c[i+j],mul(x,y))
   for k in range(2*p-2,p-1,-1):
    c[k-p]=add(c[k-p],neg(mul(c[k],lam)));c[k-p+1]=add(c[k-p+1],neg(c[k]))
   return c[:p]
  one=[1]+[0]*(p-1);x=[0,1]+[0]*(p-2)
  def ppow(n):
   r=one[:];a=x[:]
   while n:
    if n&1:r=pmul(r,a)
    a=pmul(a,a);n//=2
   return r
  assert ppow(N)==one
  failed=[r for r in rs if ppow(N//r)==one];tested+=1
  if failed:bad.append({'lambda_encoding':lam,'failed_prime_divisors':failed})
 out.append({'p':p,'n':2,'base_modulus':'u^2-'+str(d),'primitive_lambdas_tested':tested,'order_prime_divisors':rs,'nonprimitive_x':bad})
 print(out[-1],flush=True)
Path(__file__).with_name('finite-field-results.json').write_text(json.dumps(out,indent=2))
