from pathlib import Path
import subprocess,json,hashlib,datetime
D=Path(__file__).resolve().parent
subprocess.run(['python3','-B',str(D/'seal.py')],check=True)
r=subprocess.run(['python3','-B',str(D/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,(r.stdout,r.stderr)
b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'verifier_stdout':r.stdout.strip(),'verifier_stderr':r.stderr.strip(),'negative_tests':json.loads((D/'negative-tests.json').read_text()),'integrity_not_math_or_novelty':True}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
