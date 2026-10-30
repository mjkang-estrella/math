from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent; L=P.parent
S=L/'sol-kazemi-hypercube-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify(rows):
 for row in rows:
  p=Path(row['path']);assert p.stat().st_size==row['bytes'],str(p);assert sha(p)==row['sha256'],str(p)
 return len(rows)
f=json.loads((L/'root-r152-preliminary-freeze-r1/review-freeze.json').read_text())['files']
e=json.loads((S/'provenance.json').read_text())['evidence_files']
before={'candidate':verify(f),'review_evidence':verify(e)}
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'independent_check.py',Q/'independent_check.py')
r=subprocess.run([sys.executable,str(Q/'independent_check.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr)
a=json.loads((S/'independent-results.json').read_text());b=json.loads((Q/'independent-results.json').read_text())
a.pop('utc');b.pop('utc');assert a==b
after={'candidate':verify(f),'review_evidence':verify(e)};assert before==after
out={'status':'PASS','before':before,'after':after,'independent_results_equal_except_utc':True,'review_sha256':sha(S/'review.md'),'provenance_sha256':sha(S/'provenance.json'),'credit':0,'formal_pass':False}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
