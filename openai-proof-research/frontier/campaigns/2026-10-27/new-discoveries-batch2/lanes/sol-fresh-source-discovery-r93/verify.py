from pathlib import Path
import hashlib,subprocess,sys,json
p=Path(__file__).resolve().parent
for line in (p/'manifest.sha256').read_text().splitlines():
 h,name=line.split('  ',1);assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
out=subprocess.check_output([sys.executable,str(p/'check.py')],cwd=p)
assert json.loads(out)==json.loads((p/'check-results.json').read_text())
print('PASS: sealed payload and exact bounded checks. No universal theorem certified.')
