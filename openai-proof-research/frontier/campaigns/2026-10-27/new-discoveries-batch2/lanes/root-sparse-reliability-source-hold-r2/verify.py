from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime,runpy
P=Path(__file__).resolve().parent;S=P.parent/'sol-sparse-reliability-source-prior-review-r2'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'final-manifest.json').read_text());rows=json.loads((S/'freeze-before.json').read_text())['files']
ex=m.get('excludes',m.get('exclusions'))
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(ex)==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h,n
def originals():
 for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256'],r['original']
originals()
shutil.copyfile(S/'verify.py',P/'predecessor_checker.py')
j=runpy.run_path(str(P/'predecessor_checker.py'));out=j['check']()
assert out==json.loads((S/'manifest-verification.json').read_text())['diagnostics']
(P/'independent-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),original_copy_pairs=len(rows),frozen_files=len(freeze),private_diagnostics='PASS',qualification='Integrity and exact diagnostics only; dispositions recorded separately, no credit.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
