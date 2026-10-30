from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r196'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text())
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['excluded'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h,n
rows=json.loads((S/'scientific-input-freeze.json').read_text())
assert json.loads((S/'scientific-freeze.json').read_text())['pairs']==rows
def originals():
 for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256'],r
originals()
for base in ['checks','correlation-checks']:
 shutil.copyfile(S/(base+'.py'),P/(base+'.py'))
 with (P/(base+'.stdout')).open('w') as f:subprocess.run([sys.executable,str(P/(base+'.py'))],stdout=f,check=True)
 assert (P/(base+'.json')).read_bytes()==(S/(base+'.json')).read_bytes()
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),scientific_original_copy_pairs=len(rows),frozen_files=len(freeze),private_replays='both byte-identical',qualification='Finite diagnostics only; independent full-proof/source/substantive review pending.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
