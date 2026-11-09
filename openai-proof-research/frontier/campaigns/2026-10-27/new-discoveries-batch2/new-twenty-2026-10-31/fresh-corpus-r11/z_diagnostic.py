from pathlib import Path
import numpy as np, math, time,json
p=Path(__file__).parent;t=time.time();rows=[]
for g in [14,15]:
 n=2**g+1;out=[]
 for prime in range(2,math.isqrt(n)+1):
  if any(prime%q==0 for q in range(2,math.isqrt(prime)+1)):continue
  a=np.zeros(n,dtype=np.int16);v=prime
  while v<=n:a[v-1::v]+=1;v*=prime
  for length in range(n,1,-1):np.subtract(a[:length-1],a[1:length],out=a[:length-1]);np.abs(a[:length-1],out=a[:length-1])
  v=n;e=0
  while v%prime==0:v//=prime;e+=1
  out.append([prime,int(a[0]),e%2])
 rows.append(dict(g=g,small_prime_valuations=out,match=all(x[1]==x[2] for x in out)))
(p/'z-diagnostics.json').write_text(json.dumps(dict(seconds=time.time()-t,rows=rows,scope='exact integer Python/NumPy diagnostics, not Lean certificate; primes above sqrt(n) reduce to binary initial valuations and parity lemma'),indent=2));print([(r['g'],r['match']) for r in rows])
