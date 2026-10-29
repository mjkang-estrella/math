import json,hashlib,math
from fractions import Fraction
from pathlib import Path
L=Path(__file__).resolve().parent
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def shift(a,s):
 b=a+[0]*s
 for i,x in enumerate(a):b[i+s]+=x
 return b
def delta(a,k):
 def at(i):return a[i] if 0<=i<len(a) else 0
 return at(k)**2-at(k-1)*at(k+1)
d=[1];Ds={};witness=[]
for n in range(1,13):
 s=n
 while True:
  d=shift(d,s)
  if s%2:break
  s//=2
 independent=[1]
 for i in range(1,n+1):
  for j in range((n//i).bit_length()):independent=shift(independent,i)
 assert d==independent and d==d[::-1]
 Ds[n]=d
 bad=[k for k in range(1,len(d)-1) if delta(d,k)<0]
 if bad:witness.append({'n':n,'k':bad[0],'triple':d[bad[0]-1:bad[0]+2]})
assert [x['n'] for x in witness]==[3,5,6,7]
a=Ds[8];mixed=2*a[9]*a[0]-a[8]*a[1]
assert (mixed,delta(a,9),delta(Ds[9],9))==(-206,1228,1023)
# Finite Taylor diagnostics for the already-public Agoh witness, never an all-n proof.
jets=[]
for n in range(1,9):
 total=[Fraction(0)]*(n+1)
 for i in range(n+1):
  f=[math.comb(i,k) if k<=i else 0 for k in range(n+1)];f[0]-=2
  sq=mul(f,f)[:n+1]
  inv=[Fraction(1)]
  for k in range(1,n+1):inv.append(-sum(sq[j]*inv[k-j] for j in range(1,k+1)))
  for k in range(n+1):total[k]+=(-1)**i*math.comb(n,i)*inv[k]
 assert all(x==0 for x in total[:n])
 jets.append({'n':n,'vanishing_coefficients':n,'first_possible_coefficient':str(total[n])})
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
for r in http:
 if 'copy' in r:
  data=(L/r['copy']).read_bytes();assert len(data)==r['bytes'] and hashlib.sha256(data).hexdigest()==r['sha256']
lock=json.loads((L/'scientific-freeze.json').read_text())
for r in lock:
 data=(L/r['path']).read_bytes();assert hashlib.sha256(data).hexdigest()==r['sha256'] and len(data)==r['bytes']
result={'status':'PASS','credit':0,'denominator_reconstructions':12,'exception_witnesses':witness,'old_mixed_obstruction':{'mixed':mixed,'input_delta':1228,'output_delta':1023},'agoh_public_witness_finite_jets':jets,'http_receipts_verified':len(http),'scientific_files_verified':len(lock),'scope':'Reproduction diagnostics only. No universal source proof, freshness clearance, or external Lean replay.'}
(L/'check-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
