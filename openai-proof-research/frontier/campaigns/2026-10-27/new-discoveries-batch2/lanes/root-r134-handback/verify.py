from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r134'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())
def verify():
 for p,r in m.items():assert sha(S/p)==r['sha256'] and (S/p).stat().st_size==r['bytes'],p
verify();shutil.copy2(S/'checks.py',P/'copied-checks.py')
r=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(r.stdout+r.stderr);j=json.loads((P/'checks.json').read_text())
assert j==json.loads((S/'checks.json').read_text()) and j['matrix_pairs']==6561 and j['status']=='PASS'
lock=json.loads((S/'scientific-freeze.json').read_text())
for p,h in lock.items():assert sha(S/p)==h,p
verify()
(P/'ADOPTION.json').write_text(json.dumps({'status':'UNRESOLVED','credit':0,'counts':[9,39],'manifest_entries':len(m),'scientific_freeze_entries':len(lock),'copied_checker':'PASS','matrix_pairs':6561,'qualification':'Known finite algebras and method obstructions only; arbitrary-dimensional equivalence and generation remain unproved.'},indent=2)+'\n');print((P/'ADOPTION.json').read_text())
