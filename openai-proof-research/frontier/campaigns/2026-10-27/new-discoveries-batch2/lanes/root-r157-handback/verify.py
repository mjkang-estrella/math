from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r157'
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
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr);b=json.loads(r.stdout);assert b==json.loads((S/'checks.json').read_text())
after=verify();assert before==after
out={'status':'PASS','before':before,'after':after,'checks_equal':True,'variation_controls':len(b['exact_variations']),'rational_controls':b['rational_controls'],'symbolic_identities':b['symbolic_identities'],'source_resolution':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
