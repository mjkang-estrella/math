from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r130';D=P/'copy-r130';D.mkdir(exist_ok=True)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())['files']
for r in m:assert sha(S/r['path'])==r['sha256']
lock=json.loads((S/'scientific-freeze.json').read_text())['files']
for n in ['audit.py','scientific-freeze.json']+[r['path'] for r in lock]:
 d=D/n;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(S/n,d)
r=subprocess.run([sys.executable,str(D/'audit.py'),'checks'],capture_output=True,text=True,check=True)
(P/'r130-checks.log').write_text(r.stdout+r.stderr)
j=json.loads((D/'check-results.json').read_text());old=json.loads((S/'check-results.json').read_text())
assert j==old and j['status']=='PASS' and len(j['finite_recursion'])==13
for r in m:assert sha(S/r['path'])==r['sha256']
(P/'R130-ADOPTION.json').write_text(json.dumps({'credit':0,'manifest_entries':len(m),'source_hashes':len(lock),'copied_Ulam_recursion':'PASS through length14','counts':[9,39],'qualification':'No all-modulus limit, all-degree Galois theorem or ultrafilter separation proved.'},indent=2)+'\n')
print((P/'R130-ADOPTION.json').read_text())
