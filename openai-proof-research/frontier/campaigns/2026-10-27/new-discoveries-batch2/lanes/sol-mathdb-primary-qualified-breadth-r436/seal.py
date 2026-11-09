from pathlib import Path
import json,hashlib,subprocess,sys,datetime
O=Path(__file__).parent.resolve();excluded={'manifest.json','final-receipt.json'}
rows=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in excluded:
  b=p.read_bytes();rows.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(O/'manifest.json').write_text(json.dumps({'files':rows,'excluded_exact_relative_paths':sorted(excluded)},indent=2)+'\n')
p=subprocess.run([sys.executable,'-B',str(O/'verify.py')],capture_output=True,text=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'manifest_sha256':hashlib.sha256((O/'manifest.json').read_bytes()).hexdigest(),'resource_guard':'outer execution under required helper_guard.py; unmodified fixed caps','acceptance_or_novelty_claim':False}
(O/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(p.returncode)
