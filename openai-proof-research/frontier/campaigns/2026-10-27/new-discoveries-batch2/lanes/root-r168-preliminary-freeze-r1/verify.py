from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/"sol-fresh-source-discovery-r168"
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for name in ["finalmanifest.json","scientific-freeze.json"]:
  rows=json.loads((S/name).read_text())['files']
  if isinstance(rows,dict):
   for path,h in rows.items():assert sha(S/path)==h,path
  else:
   for r in rows:
    p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
  counts[name]=len(rows)
 return counts
before=verify()
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],capture_output=True,text=True,check=True)
(P/'checker.log').write_text(r.stdout+r.stderr)
assert (Q/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
after=verify();assert before==after
files=[]
for p in sorted(S.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts:files.append({'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)})
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','before':before,'after':after,'freeze_paths':len(files),'formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
