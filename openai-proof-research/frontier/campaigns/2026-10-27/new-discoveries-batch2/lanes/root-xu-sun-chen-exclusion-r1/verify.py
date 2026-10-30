from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent; L=P.parent
R=L/'sol-xu-sun-chen-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for base,manifest in [(L/'sol-fresh-source-discovery-r160',L/'root-r160-preliminary-freeze-r1/review-freeze.json'),(R,R/'final-hashes.json')]:
  rows=json.loads(manifest.read_text())['files']
  for row in rows:
   p=base/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],str(p)
  counts[base.name]=len(rows)
 return counts
before=verify(); Q=P/'replay';(Q/'frozen').mkdir(parents=True,exist_ok=True)
shutil.copyfile(R/'independent_checks.py',Q/'independent_checks.py')
shutil.copyfile(R/'frozen/certificate.json',Q/'frozen/certificate.json')
r=subprocess.run([sys.executable,str(Q/'independent_checks.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr)
a=json.loads((R/'independent-results.json').read_text());b=json.loads((Q/'independent-results.json').read_text())
a.pop('utc');b.pop('utc');assert a==b and b['status']=='PASS'
after=verify();assert before==after
out={'status':'PASS','before':before,'after':after,'independent_results_equal_except_utc':True,'quotient_coefficients':len(b['Q_low_to_high']),'minimum':b['minimum'],'constant':b['constant'],'formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
