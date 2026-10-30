from pathlib import Path
import json,hashlib,subprocess,datetime
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text());assert set(m['exclusions'])=={'finalmanifest.json','verification-receipt.json'}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['exclusions'])
assert actual==set(m['files'])
for n,h in m['files'].items():assert sha((L/n).read_bytes())==h,n
bindings=json.loads((L/'scientific-bindings.json').read_text())['records']
for r in bindings:assert sha(Path(r['original']).read_bytes())==sha((L/r['copy']).read_bytes())==r['sha256'],r
hist=json.loads((L/'qualified-original-index.json').read_text())['records'];drift=[]
for r in hist:
 if r.get('missing'):continue
 assert sha(Path(r['snapshot_reference']).read_bytes())==r['sha256'],r
 p=Path(r['original'])
 if not p.exists() or sha(p.read_bytes())!=r['sha256']:drift.append(str(p))
aliases=json.loads((L/'alias-refresh.json').read_text())['records']
for r in aliases:
 if not r.get('missing'):assert sha(Path(r['snapshot_reference']).read_bytes())==r['sha256'],r
for r in json.loads((L/'index-bindings.json').read_text()):assert sha((L/r['copy']).read_bytes())==r['sha256']
ret=subprocess.run(['python',str(L/'checks.py')],capture_output=True,timeout=180)
assert ret.returncode==0,ret.stderr.decode();assert ret.stdout==(L/'checks.json').read_bytes();assert ret.stderr==(L/'checks.stderr').read_bytes()
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),manifest_files=len(m['files']),scientific_original_copy_bindings=len(bindings),historical_snapshots=len(hist),alias_snapshots=len(aliases),historical_original_drift=drift,replay_sha256=sha(ret.stdout),explicit_exclusions=m['exclusions'],limits='Historical originals are mutable snapshots only; sampled RSS guard does not exclude unsampled transients')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
