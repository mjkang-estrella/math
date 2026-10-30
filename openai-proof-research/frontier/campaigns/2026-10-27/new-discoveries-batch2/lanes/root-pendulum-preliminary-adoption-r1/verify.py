from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-pendulum-time-map-preliminary-review-r1'
F=P.parent/'root-r166-preliminary-freeze-r1'/'review-freeze.json'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 original=json.loads(F.read_text())['files'];review=json.loads((S/'finalmanifest.json').read_text())['files']
 for root,rows in [(Path('/'),original),(S,review)]:
  for r in rows:
   p=root/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
 return {'originals':len(original),'review_manifest':len(review)}
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True)
shutil.copyfile(S/'independent_checks.py',Q/'independent_checks.py')
r=subprocess.run([sys.executable,str(Q/'independent_checks.py')],capture_output=True,text=True,check=True)
(P/'checker.log').write_text(r.stdout+r.stderr)
assert (Q/'independent-checks.json').read_bytes()==(S/'independent-checks.json').read_bytes()
after=verify();assert before==after
files=[]
for p in sorted(S.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts:files.append({'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)})
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','before':before,'after':after,'byte_identical_results':True,'review_freeze_paths':len(files),'interval_certificate':False,'formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
