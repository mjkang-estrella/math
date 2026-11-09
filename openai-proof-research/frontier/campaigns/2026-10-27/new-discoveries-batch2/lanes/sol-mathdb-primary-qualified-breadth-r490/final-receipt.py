from pathlib import Path
import subprocess,sys,json,hashlib,datetime
O=Path(__file__).resolve().parent;G=O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
p=subprocess.run([sys.executable,str(G),sys.executable,str(O/'verify.py')],capture_output=True,text=True)
receipt=dict(date=datetime.datetime.now(datetime.timezone.utc).isoformat(),command=[str(G),sys.executable,str(O/'verify.py')],exit=p.returncode,stdout=p.stdout,stderr=p.stderr,manifest_sha256=hashlib.sha256((O/'manifest.json').read_bytes()).hexdigest(),verifier_sha256=hashlib.sha256((O/'verify.py').read_bytes()).hexdigest(),negative_tests=json.loads((O/'negative-tests.json').read_text()),status='PASS' if p.returncode==0 else 'FAIL',scope='Independent integrity verification only; mathematics and novelty not certified; no upstream verifier executed')
(O/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(p.returncode)
