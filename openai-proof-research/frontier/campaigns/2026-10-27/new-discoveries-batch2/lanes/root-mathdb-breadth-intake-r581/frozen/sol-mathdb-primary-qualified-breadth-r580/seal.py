from pathlib import Path
import hashlib,json,subprocess,sys,datetime
D=Path(__file__).resolve().parent
excluded={'manifest.json','final-verification-receipt.json'}
def H(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(D)),size=len(b),sha256=hashlib.sha256(b).hexdigest())
m=dict(excluded_exact_paths=sorted(excluded),files=[H(p) for p in sorted(D.rglob('*')) if p.is_file() and str(p.relative_to(D)) not in excluded]);(D/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
p=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True);print(p.stdout,p.stderr);assert p.returncode==0
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest=H(D/'manifest.json'),verification=json.loads(p.stdout),verifier_exit=p.returncode,negative_tests=json.loads((D/'negative-tests.json').read_text()),limits='fixed helper_guard.py unchanged; 512MiB, CPU210s, wall230s',integrity_not_mathematical_or_novelty_pass=True)
(D/'final-verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r['manifest']))
