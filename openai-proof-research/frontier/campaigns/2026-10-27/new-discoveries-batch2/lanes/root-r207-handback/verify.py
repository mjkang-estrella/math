from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r207'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text())
assert set(m['exclusions'])=={'finalmanifest.json','verification-receipt.json'}
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['exclusions'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h
rows=json.loads((S/'scientific-bindings.json').read_text())
def originals():
 for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256'],r['original']
originals();drift=[];refs=[]
for name in ['qualified-original-index.json','alias-refresh.json']:
 for r in json.loads((S/name).read_text())['records']:
  if r.get('missing'):continue
  p=S/r['copy'] if 'copy' in r else Path(r['snapshot_reference'])
  assert sha(p)==r['sha256'];refs.append(dict(path=str(p),sha256=r['sha256']))
  orig=Path(r['original'])
  if not orig.exists() or sha(orig)!=r['sha256']:drift.append(r['original'])
(P/'snapshot-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
originals()
for r in refs:assert sha(Path(r['path']))==r['sha256']
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),scientific_pairs=len(rows),snapshot_references=len(refs),live_snapshot_drift=drift,frozen_files=len(freeze),private_replay='byte-identical',qualification='Rational profile and gap controls only; no universal lower-spectrum realization. Frozen references verified separately from live historical report drift.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
