import json,math
from pathlib import Path
from sympy import primerange,isprime
from sympy.ntheory.modular import crt
from sympy.combinatorics import Permutation,PermutationGroup
L=Path(__file__).resolve().parent
def rev(n,q):return Permutation(list(range(q-1,-1,-1))+list(range(q,n)))
def orbits(n,m,k):
 adj=[set() for _ in range(n)]
 for q in [n,m,k]:
  for x in range(q):adj[x].add(q-1-x)
 seen=set();out=[]
 for x in range(n):
  if x in seen:continue
  seen.add(x);todo=[x];part=[]
  while todo:
   y=todo.pop();part.append(y+1)
   for z in adj[y]-seen:seen.add(z);todo.append(z)
  out.append(sorted(part))
 return out
controls=0
for n in range(5,61):
 for k in range(2,(n-3)//2+1):
  for a in range(1,k+2):
   if math.gcd(a,n-k)==1:
    assert len(orbits(n,n-a,k))==1,(n,k,a);controls+=1
upper=[]
for n in range(4,13):
 for k in range(2,n-1):
  ms=[]
  for m in range(k+1,n):
   G=PermutationGroup([rev(n,q) for q in [n,m,k]])
   if G.order()==math.factorial(n):ms.append(m)
  assert len(ms)<=(k+1 if k%2==0 else (k+1)//2)
  upper.append([n,k,ms])
prime_controls=[]
for k in range(2,21):
 primes=list(primerange(3,k+2));mods=[4]+primes;rs=[3]+[next(c for c in range(l) if c!=0 and c!=k%l) for l in primes]
 r,M=map(int,crt(mods,rs));p=r+max(0,((2*k+1)**2-r)//M+1)*M
 trials=0
 while not isprime(p):p+=M;trials+=1;assert trials<10000
 A=list(range(1,k+2)) if k%2==0 else list(range(1,k+1,2))
 assert p>(2*k+1)**2 and p%4==3 and math.gcd(r,M)==1
 assert all(math.gcd(a,p-k)==1 for a in A)
 prime_controls.append(dict(k=k,r=r,M=M,p=p,A=A,tests=trials+1))
false_shortcuts=[]
for n,m,k in [(19,16,4),(13,12,4),(8,5,3)]:
 G=PermutationGroup([rev(n,q) for q in [n,m,k]])
 row=dict(n=n,m=m,k=k,order=int(G.order()),symmetric_order=math.factorial(n),orbits=orbits(n,m,k));false_shortcuts.append(row)
 assert row['order']<row['symmetric_order']
out=dict(transitivity_controls=controls,upper_controls=upper,prime_controls=prime_controls,falsified_shortcuts=false_shortcuts,scope='Exact finite diagnostics only; no proof of universal source statement from checking.')
(L/'route-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',controls,'transitivity controls;',len(upper),'full group row controls;',len(prime_controls),'CRT prime controls; 3 false shortcuts')
