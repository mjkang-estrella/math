from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r155'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for name in ['finalmanifest.json','scientific-freeze.json']:
  rows=json.loads((S/name).read_text())['files']
  for f,h in rows.items():assert sha(S/f)==h,f
  counts[name]=len(rows)
 return counts
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr)
a=json.loads((S/'checks.json').read_text());b=json.loads((Q/'checks.json').read_text());a.pop('utc');b.pop('utc');assert a==b
assert all(c['status']=='witness' for c in b['cases'])
after=verify();assert before==after
out={'status':'PASS','before':before,'after':after,'checks_equal_except_utc':True,'witnesses':len(b['cases']),'restricted_screen':b['restricted_screen'],'universal_proof':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
