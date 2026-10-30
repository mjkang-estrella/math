from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r159'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for name in ['finalmanifest.json','scientific-freeze.json']:
  rows=json.loads((S/name).read_text())['entries']
  for f,r in rows.items():
   p=S/f;assert sha(p)==(r['sha256'] if isinstance(r,dict) else r),f
   if isinstance(r,dict):assert p.stat().st_size==r['bytes'],f
  counts[name]=len(rows)
 return counts
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr);assert (Q/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
after=verify();assert before==after;b=json.loads((Q/'checks.json').read_text())
out={'status':'PASS','before':before,'after':after,'byte_identical_checks':True,'graphs':b['graphs'],'vertex_identity_checks':b['vertex_identity_checks'],'expectation_method_falsified':b['expectation_method_falsified'],'source_resolution':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
