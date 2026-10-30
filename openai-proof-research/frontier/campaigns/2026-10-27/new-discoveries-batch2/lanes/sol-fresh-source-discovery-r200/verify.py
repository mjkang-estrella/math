from pathlib import Path
import json,hashlib,datetime,subprocess,sys
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
excluded={'finalmanifest.json','verification-receipt.json'}
m=json.loads((L/'finalmanifest.json').read_text());assert set(m['exclusions'])==excluded
files=m['files']; actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
assert set(files)==actual
for n,h in files.items():assert sha((L/n).read_bytes())==h,n
rr=json.loads((L/'scientific-freeze.json').read_text())+json.loads((L/'primary-freeze.json').read_text())
def pairs():
    for r in rr:assert sha(Path(r['original']).read_bytes())==r['sha256']==sha((L/r['copy']).read_bytes()),r['original']
pairs()
p=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,check=True)
assert p.stdout==(L/'checks.json').read_bytes()
pairs()
for n,h in files.items():assert sha((L/n).read_bytes())==h,n
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),manifest_files=len(files),original_copy_pairs=len(rr),original_copy_before_after='PASS for actual final freezes only',exact_replay='BYTE_IDENTICAL',exclusions=sorted(excluded),limits='First primary-body reads preceded copy freezing; no retroactive first-read PASS. Administrative live documents are not scientific inputs. Bounded coverage is not all-history clearance. No full source proof.')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
