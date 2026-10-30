from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-sparse-reliability-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'final-manifest.json').read_text());rows=json.loads((S/'freeze-before.json').read_text())['inputs']
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['excludes'])=={r['path'] for r in m['entries']}
for r in m['entries']:assert sha(S/r['path'])==r['sha256'] and (S/r['path']).stat().st_size==r['bytes']
def originals():
 for r in rows:
  for p in [Path(r['original']),S/r['copy']]:assert sha(p)==r['sha256'] and p.stat().st_size==r['size']
originals();shutil.copyfile(S/'independent_check.py',P/'independent_check.py')
with (P/'checker.stdout').open('w') as f:subprocess.run([sys.executable,str(P/'independent_check.py')],stdout=f,check=True)
assert (P/'independent-evidence.json').read_bytes()==(S/'independent-evidence.json').read_bytes()
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['entries']),original_copy_pairs=len(rows),frozen_files=len(freeze),private_replay='byte-identical',qualification='Independent finite diagnostics only; ordinary proof separately read. Novelty remains HOLD.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
