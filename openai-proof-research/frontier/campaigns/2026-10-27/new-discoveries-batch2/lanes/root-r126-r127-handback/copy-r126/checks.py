import json,hashlib,gzip,sqlite3,time,sys
from pathlib import Path
from fractions import Fraction as F
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check():
 receipts=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
 for r in receipts:
  p=L/r['copy'];assert p.stat().st_size==r['bytes'];assert sha(p)==r['sha256']
 for r in json.loads((L/'source-lock.json').read_text()):assert sha(L/r['copy'])==r['sha256']
 assert (L/'sources/wallis-public-result.lean').read_bytes()==(L/'sources/cached-wallis-Result.lean').read_bytes()
 # Exact finite checks of the already-public Wallis Stieltjes algebra.
 n=0
 for x in [F(1,3),F(1),F(7,2)]:
  for q in [F(1,5),F(1,2),F(3,4)]:
   z=x*x;s=(1-q/24)/z;logB=-x*s/8
   theta=F(23040,31)*x**5*(3*x/(24*z+1)+logB)
   chi=F(358400,257)*x**7*((120*z+31)/(96*x*(10*z+3))+logB)
   mu=-z-1/(24+3/x/logB)
   assert theta==-z**3*(s-1/(z+F(1,24)))/F(31,2880)
   assert chi==z**3*(q-1/(z+F(3,10)))/F(771,5600)
   assert mu==1/q-z-F(1,24)
   n+=3
 # Digamma triple-product summand subtraction in Salazar Theorem 3.1.
 for a in [F(1,3),F(2,3),F(3,2),F(7,2)]:
  for y in [F(1,4),F(1),F(5)]:
   assert a/(y*(y+a))-a/(y*(y+1))==a*(1-a)/(y*(y+1)*(y+a));n+=1
 rec=json.loads((L/'screen-receipt.json').read_text());db=sqlite3.connect(L/'screen.sqlite')
 assert db.execute('select count(*) from bodies').fetchone()[0]==rec['unique']
 aliases=0;scientific=[]
 with gzip.open(L/'pathmap.jsonl.gz','rt') as f:
  for line in f:
   h,p=json.loads(line);aliases+=1
   if any('/sol-fresh-source-discovery-r'+str(k)+'/' in p for k in (111,112,113)) and Path(p).name in {'SUMMARY.md','discovery.md','PROOF.md','review.md'}:scientific.append(p)
 assert aliases==rec['paths'];assert scientific
 assert not (L/'PROOF.md').exists()
 result=dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),pass_all=True,finite_exact_algebra_checks=n,http_bindings=len(receipts),stream_paths=aliases,unique_bodies=rec['unique'],retained_r111_r113_scientific=scientific,scope='Offline evidence and finite algebra checks, not a replay/certification of public proofs or a new theorem')
 if '--manifest' in sys.argv:
  m=json.loads((L/'finalmanifest.json').read_text())
  for p,h in m['files'].items():assert sha(L/p)==h,p
  result.update(manifest_entries=len(m['files']),manifest_sha256=sha(L/'finalmanifest.json'))
  (L/'manifest-verification.json').write_text(json.dumps(result,indent=2)+'\n')
 else:(L/'checks-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
check()
