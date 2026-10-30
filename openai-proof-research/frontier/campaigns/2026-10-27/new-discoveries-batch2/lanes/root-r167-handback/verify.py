from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r167'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for name in ['finalmanifest.json','scientific-freeze.json']:
  rows=json.loads((S/name).read_text())['files']
  for r in rows:
   p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
  counts[name]=len(rows)
 return counts
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True)
for f in ['checks.py','newton.py','checks.json','newton.json']:shutil.copyfile(S/f,Q/f)
for f in ['checks.py','newton.py']:
 r=subprocess.run([sys.executable,str(Q/f),'verify'],capture_output=True,text=True,check=True)
 (P/(f+'.log')).write_text(r.stdout+r.stderr)
after=verify();assert before==after
rows=json.loads((Q/'newton.json').read_text())['rows'];assert len(rows)==46 and all(not r['remaining_factor_degrees'] for r in rows)
out={'status':'PASS','before':before,'after':after,'finite_newton_cases':len(rows),'full_scope_proof':False,'formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
