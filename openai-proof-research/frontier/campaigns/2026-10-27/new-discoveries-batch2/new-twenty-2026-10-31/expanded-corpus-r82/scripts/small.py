from fetch import D
import math,json,collections,sys
from fractions import Fraction
import sympy as s
O={}
def put(i,space,result,kind='exact bounded diagnostic'):
 O[str(i)]={'space':space,'result':result,'kind':kind};(D/'outputs/small.json').write_text(json.dumps(O,indent=2)+'\n');print(i,space,str(result)[:400],flush=True)
N=1000000
spf=list(range(N+1))
for p in range(2,math.isqrt(N)+1):
 if spf[p]==p:
  for j in range(p*p,N+1,p):
   if spf[j]==j:spf[j]=p
primes=[p for p in range(2,N+1) if spf[p]==p]
def factors(n):
 d={}
 while n>1:p=spf[n];d[p]=d.get(p,0)+1;n//=p
 return d
phi=list(range(10001))
for p in primes:
 if p>10000:break
 for j in range(p,10001,p):phi[j]-=phi[j]//p
classes=collections.defaultdict(list)
for n in range(1,10001):classes[phi[n]].append(n)
put(316046,'all 1<=n<=1000, partners tested among 1<=m<=10000',[n for n in range(1,1001) if len(classes[phi[n]])<2])
# Maximal consecutive composite runs; Hall matching for maximal run implies all subintervals.
runs=[];run=[]
for n in range(2,10001):
 if spf[n]!=n:run.append(n)
 elif run:runs.append(run);run=[]
if run:runs.append(run)
def match(run):
 owner={}
 def aug(n,seen):
  for p in factors(n):
   if p in seen:continue
   seen.add(p)
   if p not in owner or aug(owner[p],seen):owner[p]=n;return True
  return False
 return all(aug(n,set()) for n in run)
put(316050,'all composite intervals contained in [2,10000], via maximal-run prime-factor bipartite matching',{'runs':len(runs),'failures':[r for r in runs if not match(r)]})
p=[0]*2001;p[0]=1
for k in range(1,2001):
 for n in range(k,2001):p[n]+=p[n-k]
put(316055,'p(n) for 0<=n<=2000; moduli 1<=m<=100',{'missing':{m:sorted(set(range(m))-{v%m for v in p}) for m in range(1,101) if len({v%m for v in p})<m}},'finite residue sample cannot refute infinitude')
def chain(target):
 if target==1:return 0
 def rec(a,left):
  if a[-1]==target:return True
  if not left or a[-1]*(2**left)<target:return False
  for v in sorted({x+y for x in a for y in a if a[-1]<x+y<=target},reverse=True):
   if rec(a+[v],left-1):return True
  return False
 for depth in range(target.bit_length()-1,2*target.bit_length()):
  if rec([1],depth):return depth
put(316056,'all increasing addition chains needed for exact l(n),l(2^n-1), 1<=n<=8',[{'n':n,'lhs':chain(2**n-1),'rhs':n-1+chain(n)} for n in range(1,9)])
c=collections.Counter(math.comb(n,k) for n in range(2,301) for k in range(1,n))
put(316057,'all interior Pascal positions 2<=n<=300',{'max_truncated_multiplicity':max(c.values()),'values':[a for a,v in c.items() if v==max(c.values())]},'bounded sample cannot refute existence of uniform constant')
powers=sorted({x**k for k in range(2,20) for x in range(1,1001) if x**k<=N})
put(316111,'all perfect-power VALUES <=1000000; exponents<=19 suffice for base>=2',{'count':len(powers),'last_gaps':[b-a for a,b in zip(powers,powers[1:])][-20:]},'gap sample cannot refute limit; base=1 representation defect excluded')
put(316114,'all 2<=n<=2000 direct power-sum congruence',[n for n in range(2,2001) if ((sum(pow(i,n-1,n) for i in range(1,n))%n==n-1)!=(spf[n]==n))])
put(316121,'all 1<=n<=999998; powerful membership by prime exponents',[n for n in range(1,N-1) if all(all(e>=2 for e in factors(x).values()) for x in (n,n+1,n+2))])
ps=[p for p in primes if p<=100]
put(316122,'all ordered distinct primes p,q<=100',[ [p,q] for p in ps for q in ps if p!=q and ((q**p-1)//(q-1))%((p**q-1)//(p-1))==0])
def prime(n):return n>=2 and s.isprime(n)
put(316130,'all odd 1<=p<=61; (i) k in 0..7 suffices', [p for p in range(1,62,2) if sum([any(p in (2**k+1,2**k-1,4**k+3,4**k-3) for k in range(8)),prime(2**p-1),prime((2**p+1)//3)])==2])
put(318577,'all 1<=n<=999, sieve covers (n+1)^2',[n for n in range(1,1000) if sum(spf[k]==k for k in range(n*n+1,(n+1)**2))<2])
prod=Fraction(1)
fail=[]
for n in range(1,1001):
 k=(n&-n).bit_length()-1;odd=n>>k;prod*=Fraction(odd)**(1-k)
 if prod>=4**n:fail.append(n)
put(319785,'all 1<=n<=1000; exact rational product f(2^k*l)=l^(1-k)',fail)
# Stern B, not the different 0/1 Stern polynomials.
t=s.Symbol('t');B=[s.Poly(0,t),s.Poly(1,t)]
fail=[]
for n in range(2,10001):
 b=B[n//2].mul(s.Poly(t,t)) if n%2==0 else B[n//2]+B[n//2+1]
 B.append(b)
 if spf[n]==n and not b.is_irreducible:fail.append([n,str(b.as_expr())])
put(321201,'all prime p<=10000; B0=0 B1=1 B2n=t*Bn B2n+1=Bn+B(n+1); exact Q[t] factor test',fail)
