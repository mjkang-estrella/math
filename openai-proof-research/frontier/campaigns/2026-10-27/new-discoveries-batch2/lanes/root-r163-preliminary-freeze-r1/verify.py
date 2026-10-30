from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r163'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for name in ['finalmanifest.json','scientific-freeze.json']:
  rows=json.loads((S/name).read_text())['entries']
  for r in rows:
   p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
  counts[name]=len(rows)
 return counts
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True)
shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr)
assert (Q/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
b=json.loads((Q/'checks.json').read_text());assert b['status']=='PASS'
after=verify();assert before==after
files=[]
for p in sorted(S.rglob('*')):
 if not p.is_file() or '__pycache__' in p.parts:continue
 files.append({'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)})
(P/'review-freeze.json').write_text(json.dumps({'root':str(S),'files':files},indent=2)+'\n')
out={'status':'PASS','before':before,'after':after,'byte_identical_checks':True,'controls':b,'review_freeze_paths':len(files),'credit':0,'formal_pass':False}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
