"""Exact rational supporting checks, never an all-order proof or novelty test."""
from fractions import Fraction as Q
from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
def alt(s,x,M=32):
 # a(k)=(x+k)^(-s) is a Hausdorff moment sequence. Euler's
 # transformation has nonnegative forward differences <=a(0).
 # The omitted terms j>=M sum to <= a(0)/2**M.
 row=[1/(x+k)**s for k in range(M)];a0=row[0];lo=Q(0)
 for j in range(M):
  assert all(a>0 for a in row)
  lo+=row[0]/2**(j+1)
  row=[a-b for a,b in zip(row,row[1:])]
 return lo,lo+a0/2**M
def F(n,x):
 a,b=alt(n+1,x);c,d=alt(n+2,x)
 return -x*(n+1)*d/a,-x*(n+1)*c/b
def enc(interval):return [str(x) for x in interval]
rows=[]
for n in range(13):
 xs=[Q(1,4),Q(n+1),Q(100*(n+1))];v=[F(n,x) for x in xs]
 assert v[1][1]<v[0][0] and v[1][1]<v[2][0],(n,v)
 assert all(b<-(n+1) for a,b in v)
 rows.append({'n':n,'x':list(map(str,xs)),'F_intervals':list(map(enc,v)),'middle_below_both':True})
v=[F(1,Q(i)) for i in (1,2,3)]
assert v[0][0]>v[1][1] and v[2][0]>v[1][1]
sources=[]
for line in (L/'http.jsonl').open():
 r=json.loads(line)
 if 'copy' in r:
  p=L/r['copy'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];sources.append(r['copy'])
result={'status':'PASS','source_hashes_checked':sources,'orders_checked':13,'Euler_terms':32,'all_order_proof':False,'rows':rows,'published_n1_witness':list(map(enc,v))}
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 13 exact three-point interval witnesses; published n=1 witness; primary HTTP-byte hashes')
