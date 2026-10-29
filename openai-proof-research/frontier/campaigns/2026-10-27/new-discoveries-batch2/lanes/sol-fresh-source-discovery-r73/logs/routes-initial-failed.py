from math import comb,gcd,isqrt
from pathlib import Path
import json
r=Path(__file__).resolve().parent
def fs(d):
 out=[];p=2
 while p*p<=d:
  if d%p==0:
   out.append(p)
   while d%p==0:d//=p
  p+=1
 if d>1:out.append(d)
 return out
def summands(N,K,p):
 q=p;out=[]
 while q<=N:
  z=N//q-K//q-(N-K)//q
  if z:out.append(q)
  q*=p
 return out
cert=[]
for m in range(1,11):
 n=32;d=m*31+1;N=m*n*n;K=m*n
 ob=[{'p':p,'carry_powers':summands(N,K,p)} for p in fs(d) if summands(N,K,p)]
 cert.append({'m':m,'d':d,'factors':fs(d),'obstructions':ob})
 assert bool(ob)==(m<10)
assert 10**2==3*32+4
primecases=0
for n in range(2,151):
 for m in range(2,201):
  d=m*(n-1)+1
  if fs(d)!=[d]:continue
  yes=all(not summands(m*n*n,m*n,p) for p in [d])
  assert yes==(m<=n)
  primecases+=1
# Smallest-prime-power-only shortcut fails at n=8,m=2.
assert (16%3)<=128%3 and summands(128,16,3)==[9,27]
# n=20: all allowed nontrivial prime-modulus options fail, yet m=2 works.
n=20;B=isqrt(3*n+4)
assert B==8 and all(fs(m*19+1)!=[m*19+1] for m in range(2,B+1))
assert gcd(comb(800,40),39)==1
(r/'route-checks.json').write_text(json.dumps({'prime_modulus_iff_tests':primecases,'sharp_n32_certificate':cert,'primepower_shortcut_failure':{'n':8,'m':2,'p':3,'carries':[9,27]},'prime_menu_failure_n20':True},indent=2))
print('PASS',primecases,'prime-modulus equivalences; full n32 certificate; two route obstructions')
