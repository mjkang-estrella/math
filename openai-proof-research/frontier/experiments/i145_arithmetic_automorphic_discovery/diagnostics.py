"""New finite I145 instances only. No inherited module execution or I/O."""
from fractions import Fraction as F
from math import factorial, log, sqrt
from itertools import product

def run():
 grouping=[]
 for n,K in [(3,2),(3,4),(5,2),(3,400)]:
  u=F(1,17);h=K*u
  ws=[u*F(8+j%3,10) for j in range(113 if K<400 else 19)]
  costs=[u**(n-1)*w for w in ws];groups=[];used=F(0)
  for c in costs:
   if used+c>h**n:groups.append(used);used=F(0)
   used+=c
  groups.append(used);A=sum(costs);N=len(groups)
  assert all(g>h**n-u**n for g in groups[:-1])
  assert N<=A/(h**n-u**n)+1
  cubes=(N+factorial(n)-1)//factorial(n)
  assert cubes*factorial(n)*h**n<=A/(1-F(1,K**n))+factorial(n)*h**n
  grouping.append(dict(n=n,K=K,points=len(ws),groups=N,cubes=cubes))
 # Finite valuation shells of L={(x,y,z):x=y mod 2}, whose maximal hull is Z_2^3.
 shells=[]
 for t in range(2,6):
  m=2**t;counts={};inside={}
  def val(a):
   if not a:return t
   z=0
   while a%2==0:z+=1;a//=2
   return z
  for xyz in product(range(m),repeat=3):
   v=tuple(val(a) for a in xyz);counts[v]=counts.get(v,0)+1
   if (xyz[0]-xyz[1])%2==0:inside[v]=inside.get(v,0)+1
  mass=sum(F(inside.get(v,0),m**3) for v in counts)
  assert mass==F(1,2)
  truncated=sum(F(inside.get(v,0),c)*F(1,2**sum(v)) for v,c in counts.items() if max(v)<t)
  missing=F(4)-truncated
  assert missing>=0 and missing<=8*F(3,2**t)
  shells.append(dict(modulus=m,index=2,exact_mass=str(mass),truncated_shell_sum=str(truncated),omitted_shell_bound=str(missing)))
 assert all(F(shells[i+1]['omitted_shell_bound'])<F(shells[i]['omitted_shell_bound']) for i in range(3))
 # Elementary fractional divisor sum used at small ideal norms.
 divisor=[]
 for n in (3,5):
  cap=1024;d=[0]+[1]*cap
  for _ in range(n-1):
   nxt=[0]*(cap+1)
   for a in range(1,cap+1):
    for b in range(a,cap+1,a):nxt[b]+=d[b//a]
   d=nxt
  for x in (8,64,1024):
   lhs=sum(d[b]/sqrt(b) for b in range(1,x+1));rhs=2*sqrt(x)*(1+log(x))**(n-1)
   assert lhs<=rhs
   divisor.append(dict(n=n,x=x,alpha='1/2',ratio=lhs/rhs))
 # All coordinate quotient subgroups of (Z/2)^m; exact Fourier signs and Parseval.
 fourier=[];rare=[]
 for dim in range(1,7):
  h=2**dim;values=[F((i*i+3*i+1)%11,7) for i in range(h)]
  chi=lambda j,i: (-1)**((j&i).bit_count())
  FT=[sum(chi(j,i)*values[i] for i in range(h))/h for j in range(h)]
  for codim in range(dim+1):
   k=2**codim;means=[sum(values[i] for i in range(h) if i%k==c)/(h//k) for c in range(k)]
   for c in range(k):assert means[c]-FT[0]==sum(chi(j,c)*FT[j] for j in range(1,k))
   assert sum((z-FT[0])**2 for z in means)/k==sum(x*x for x in FT[1:k])
   # Jensen under the conditional expectation, centered at arbitrary constant 2/3.
   assert sum((z-F(2,3))**2 for z in means)/k<=sum((z-F(2,3))**2 for z in values)/h
   fourier.append(dict(group_order=h,index=k,exact=True))
  var=F(h-1,h*h);worst=F(h-1,h)
  assert var==F(1,h)*(1-F(1,h)) and worst*worst==(h-1)*var
  rare.append(dict(order=h,variance=str(var),worst_deviation=str(worst)))
 # Exponent accounting: k<=d^delta<=Q^(2n delta), B<=Q^(-(1-p/n)/8).
 exponents=[]
 for n in (5,7,11):
  for p in (F(1),F(n,2),F(n)-F(1,3)):
   beta=(1-p/n)/8;delta=beta/(4*n)
   assert beta-2*n*delta==beta/2>0
   exponents.append(dict(n=n,p=str(p),delta=str(delta),remaining_Q_decay=str(beta/2)))
 return dict(status='PASS',greedy_cube_checks=grouping,local_shell_checks=shells,fractional_divisor_checks=divisor,exact_character_checks=fourier,rare_coset_interface=rare,relative_tail_exponents=exponents,scope='Finite instances only; no universal mathematics, arithmetic counterexample, contribution, priority, human or formal certification')
