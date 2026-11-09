from pathlib import Path
import json,hashlib,datetime,subprocess,sys
D=Path(__file__).resolve().parent
r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
b=(D/'manifest.json').read_bytes()
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_size=len(b),verifier_exit=r.returncode,stdout=r.stdout,stderr=r.stderr,scientific_acceptance=False,novelty_cleared=False,negative_tests='negative-test-results.json',guard='fixed helper_guard.py; 512MiB AS/groupRSS CPU210s wall230s unchanged')
(D/'final-verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));sys.exit(r.returncode)
