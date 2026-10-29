from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r133'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())['files']
def verify():
 for r in m:assert sha(S/r['path'])==r['sha256'] and (S/r['path']).stat().st_size==r['bytes']
verify();shutil.copy2(S/'checks.py',P/'copied-checks.py')
r=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(r.stdout+r.stderr);j=json.loads(r.stdout)
assert j==json.loads((S/'check-results.json').read_text()) and j['exact_basis_triples']==125
lock=json.loads((S/'scientific-freeze.json').read_text())['files']
for r in lock:assert sha(S/r['path'])==r['sha256']
verify()
(P/'ADOPTION.json').write_text(json.dumps({'status':'UNRESOLVED','credit':0,'counts':[9,39],'manifest_entries':len(m),'scientific_freeze_entries':len(lock),'copied_checker':'PASS','triples':125,'qualification':'Nonperfect class-three example blocks a flattening shortcut, not the source conjecture. No full proof or novelty clearance.'},indent=2)+'\n')
print((P/'ADOPTION.json').read_text())
