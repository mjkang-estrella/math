from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r201'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text())
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['explicit_exclusions'])=={r['path'] for r in m['files']}
for r in m['files']:assert sha(S/r['path'])==r['sha256'] and (S/r['path']).stat().st_size==r['bytes']
rows=json.loads((S/'primary-freeze.json').read_text());history=json.loads((S/'history-receipt.json').read_text())['records']
def originals():
 for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
 for r in history:assert sha(S/r['copy'])==r['sha256']
originals()
drift=[r['original'] for r in history if not Path(r['original']).exists() or sha(Path(r['original']))!=r['sha256']]
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),primary_original_copy_pairs=len(rows),history_snapshot_copies=len(history),live_snapshot_drift=drift,frozen_files=len(freeze),private_replay='byte-identical',qualification='Pointwise algebra controls only; no universal rigidity theorem. Mutable historical report changes are not primary-source freeze failures.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
