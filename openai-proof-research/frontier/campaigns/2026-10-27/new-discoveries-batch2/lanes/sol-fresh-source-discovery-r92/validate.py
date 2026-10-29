from pathlib import Path
from math import comb
import json,hashlib
L=Path(__file__).resolve().parent
d=json.loads((L/'analysis-results.json').read_text());tested=0
for r in d['rows']:
 n=r['n'];a=r['a'];b=r['b']
 assert not r['LC_a_failures'] and not r['LC_b_failures']
 assert all(b[k]==a[k]+(a[k+1] if k+1<n else 0) for k in range(n))
 for k in range(2,n-1):
  tested+=1
  assert a[k]**2*comb(n-2,k-2)*comb(n-2,k)>=a[k-1]*a[k+1]*comb(n-2,k-1)**2
for r in json.loads((L/'http.json').read_text()):
 if 'sha256' in r:assert hashlib.sha256((L/r['file']).read_bytes()).hexdigest()==r['sha256']
print('All source hashes match; bounded LC and ULC checks pass:',tested)
