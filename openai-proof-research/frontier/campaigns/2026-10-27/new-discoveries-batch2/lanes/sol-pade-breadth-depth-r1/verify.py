from pathlib import Path
from fractions import Fraction as F
from math import factorial,comb
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FAIL'}
try:
 manifest=json.loads((L/'finalmanifest.json').read_text())
 assert not any(r['path'] in ['finalmanifest.json','verification-receipt.json'] for r in manifest)
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
 assert actual=={r['path'] for r in manifest}
 for r in manifest:assert sha(L/r['path'])==r['sha256'],r['path']
 refs=json.loads((L/'references.json').read_text())
 for r in refs:assert sha(Path(r['path']))==r['sha256'],r['path']
 # Independent Fraction arithmetic, using coefficient ratios instead of factorial scaling.
 def den(m):
  a=[F(1)]
  for j in range(1,m+1):a.append(-a[-1]*F(m-j+1,j*(2*m-j+1)))
  return a
 def inv(a,N):
  c=[F(1)]
  for n in range(1,N+1):
   v=F(0)
   for j in range(1,min(n,len(a)-1)+1):v-=a[j]*c[n-j]
   c.append(v)
  return c
 for m in range(1,40,2):assert all(v>0 for v in inv(den(m),80))
 a=den(11);d=[sum((a[i]*a[2*j-i]*(-1)**(2*j-i) for i in range(12) if 0<=2*j-i<12),F(0)) for j in range(12)]
 witness=inv(d,10)[10]
 assert witness==-F(21866269,9888422815022969014815189447475200)
 assert inv(a,20)[20]>0
 rows=json.loads((L/'checks.json').read_text())['sweep']
 assert [r['m'] for r in rows]==list(range(1,40,2))
 assert all(r['n_max']==400 and not r['nonpositive'] for r in rows)
 for m in range(3,40,2):
  c=inv(den(m),4)
  assert c[2]==F(m,4*(2*m-1))
  assert c[4]-c[1]*c[3]-c[2]**2/2+c[1]**2*c[2]-c[1]**4/4==-F(1,64*(2*m-1)**2*(2*m-3))
 for r in refs:assert sha(Path(r['path']))==r['sha256'],r['path']
 out.update(status='PASS',manifest_sha256=sha(L/'finalmanifest.json'),manifest_files=len(manifest),reference_bindings=len(refs),independent_fraction_scope='odd m<=39,n<=80',product_obstruction=str(witness),source_claim_status='UNRESOLVED_NO_COUNT',limitations='No full endpoint proof or complete current-registry clearance; stored sweep400 not independently fully replayed here')
except Exception as e:out['error']=repr(e)
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2));assert out['status']=='PASS'
