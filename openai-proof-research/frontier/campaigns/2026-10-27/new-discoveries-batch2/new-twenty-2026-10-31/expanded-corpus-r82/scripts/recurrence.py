from fetch import D
import math,json
c=2;fund=[2];last=0;rows=[]
for n in range(2,10000001):
 inc=math.gcd(n if n%2==0 else n-2,c);c+=inc
 if c==2*n and n>2:
  i=len(fund)+1;prev=fund[-1];rows.append({'i':i,'m':n,'previous_m':prev,'rho':last,'denominator':prev+3,'lambda':str(last)+'/'+str(prev+3),'fails_i_ge_6':i>=6 and 4*last>5*(prev+3) });fund.append(n)
 if inc>1:last=n
(D/'outputs/shevelev.json').write_text(json.dumps({'space':'all recurrence indices 1..10000000; only completed fundamental intervals assessed; final incomplete interval excluded','rows':rows,'final_c':c},indent=2));print(json.dumps(rows,indent=2))
N=1000000
sieve=bytearray(b'\1')*(N+1);sieve[:2]=b'\0\0'
for p in range(2,math.isqrt(N)+1):
 if sieve[p]:sieve[p*p:N+1:p]=b'\0'*len(range(p*p,N+1,p))
ps=[p for p in range(2,N+1) if sieve[p]];idx={p:i for i,p in enumerate(ps)};counts={i:0 for i in range(1,11)}
for n,p in enumerate(ps[:-1]):
 gap=ps[n+1]-p;l=p-gap
 if l>gap and l in idx:
  i=n-idx[l]
  if i in counts:counts[i]+=1
(D/'outputs/levels.json').write_text(json.dumps({'space':'all primes with successor <=1000000; level(1;i) via l=p_n-(p_(n+1)-p_n)=p_(n-i)>gap; i=1..10','counts':counts,'kind':'infinitude cannot be falsified by bounded sample'},indent=2));print(counts)
