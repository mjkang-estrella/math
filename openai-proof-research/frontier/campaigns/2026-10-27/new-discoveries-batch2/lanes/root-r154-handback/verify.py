from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r154'
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
before=verify();Q=P/'replay';(Q/'sources').mkdir(parents=True,exist_ok=True)
for f in ['checks.py','sources/bernoulli.pdf','sources/bernoulli-v1.pdf']:shutil.copyfile(S/f,Q/f)
r=subprocess.run([sys.executable,str(Q/'checks.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr)
assert (Q/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
after=verify();assert before==after
out={'status':'PASS','before':before,'after':after,'byte_identical_checks':True,'diagnostics':json.loads((Q/'checks.json').read_text()),'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
