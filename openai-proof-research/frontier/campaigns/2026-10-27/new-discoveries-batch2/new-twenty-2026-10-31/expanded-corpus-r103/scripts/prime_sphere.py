from pathlib import Path
import json,numpy as np,math
D=Path(__file__).resolve().parents[1]
sieve=bytearray(b'\x01')*300000;sieve[:2]=b'\0\0'
for p in range(2,548):
 if sieve[p]:sieve[p*p::p]=b'\0'*len(sieve[p*p::p])
primes=[i for i,b in enumerate(sieve) if b][:20000];a=np.array(primes,dtype=np.int64);leading=[]
while len(a)>1:a=np.abs(a[1:]-a[:-1]);leading.append(int(a[0]))
(D/'outputs/gilbreath.json').write_text(json.dumps(dict(originator='initial segment of primes starting at 2',n=len(primes),last_prime=primes[-1],leading_violations=[[i+1,a] for i,a in enumerate(leading) if a!=1],trace=sum(leading),beyond_source_range=False,limitation='No claimed extension of classical Odlyzko computation; arbitrary prime-originator wording is not used for credit'),indent=2)+'\n')
# Only necessary divisibility screens, not construction/exhaustion of spherical designs.
rows=[]
for n in range(1001,1101):
 lo=n*(n+1)*(n+2)//3;hi=lo+10000
 survivors=[M for M in range(lo+1,hi+1) if 12*M%n==0 and 4*M*M%(n+1)==0]
 rows.append(dict(n=n,M_interval=[lo+1,hi],divisibility_survivors=survivors))
(D/'outputs/sphere.json').write_text(json.dumps(dict(rows=rows,source_conditions='Corollaries 4 and 6: n|12M, n+1|4M^2',limitation='Necessary conditions only; discriminant and distance-distribution integrality untested; no design construction'),indent=2)+'\n')
print('Gilbreath',len(primes),sum(leading),set(leading));print('Sphere dimensions',len(rows),'pairs',1000000,'survivors',sum(len(r['divisibility_survivors']) for r in rows))
