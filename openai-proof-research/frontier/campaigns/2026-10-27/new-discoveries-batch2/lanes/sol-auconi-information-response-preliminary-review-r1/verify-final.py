from pathlib import Path
import hashlib,json,subprocess,sys,datetime
l=Path(__file__).resolve().parent
# Run own checker, not candidate's; then verify final bytes.
r=subprocess.run([sys.executable,str(l/'independent-check.py')],capture_output=True,text=True)
assert r.returncode==0,(r.stdout,r.stderr)
m=json.loads((l/'manifest.json').read_text())
expected={r['path'] for r in m['files']}
actual={str(p.relative_to(l)) for p in l.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==expected,(actual-expected,expected-actual)
for row in m['files']:
 p=l/row['path'];data=p.read_bytes();assert len(data)==row['bytes'];assert hashlib.sha256(data).hexdigest()==row['sha256'],row['path']
rows=json.loads((l/'before-after.json').read_text())
for row in rows:
 assert hashlib.sha256(Path(row['original']).read_bytes()).hexdigest()==row['before']
 assert hashlib.sha256((l/row['copy']).read_bytes()).hexdigest()==row['before']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256((l/'manifest.json').read_bytes()).hexdigest(),payload_files=len(m['files']),scientific_original_copy_pairs=len(rows),independent_checker='PASS exact rationals; analytic scope in review.md',excluded=['manifest.json','verification-receipt.json'],acceptance=False,counts_unchanged=[9,39,40])
(l/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
