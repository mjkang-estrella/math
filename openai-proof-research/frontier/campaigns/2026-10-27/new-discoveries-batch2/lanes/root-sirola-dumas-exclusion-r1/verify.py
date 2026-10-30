from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;R=P.parent/'sol-sirola-dumas-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for base,manifest in [(P.parent/'sol-fresh-source-discovery-r163',P.parent/'root-r163-preliminary-freeze-r1/review-freeze.json'),(R,R/'finalhashes.json')]:
  rows=json.loads(manifest.read_text())['files']
  for r in rows:
   p=base/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
  counts[base.name]=len(rows)
 return counts
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(R/'independent_check.py',Q/'independent_check.py')
r=subprocess.run([sys.executable,str(Q/'independent_check.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr)
assert (Q/'independent-evidence.json').read_bytes()==(R/'independent-evidence.json').read_bytes()
b=json.loads((Q/'independent-evidence.json').read_text());assert b['status']=='PASS'
after=verify();assert before==after
out={'status':'PASS','before':before,'after':after,'byte_identical_independent_checks':True,'checks':b,'formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
