from pathlib import Path
import json,hashlib,subprocess,sys
D=Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def seal():
 files=[]
 for p in sorted(D.rglob('*')):
  if p.is_file() and str(p.relative_to(D)) not in excluded:
   b=p.read_bytes();files.append(dict(path=str(p.relative_to(D)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
 (D/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=excluded,files=files),indent=2)+'\n')
seal();results=[]
for case in ['hash','size','extra']:
 r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--negative',case],capture_output=True,text=True)
 assert r.returncode!=0
 results.append(dict(case=case,exit_code=r.returncode,stderr=r.stderr.strip(),method='in-memory mutation of own expected manifest or actual-path set; same payload validation function; no original mutated'))
(D/'negative-test-results.json').write_text(json.dumps(results,indent=2)+'\n');seal()
r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
if r.returncode:print(r.stderr);sys.exit(r.returncode)
(D/'final-verification-receipt.json').write_text(r.stdout);print(r.stdout)
