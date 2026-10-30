from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent
number=int(P.name.split('-')[1][1:]);S=P.parent/f'sol-fresh-source-discovery-r{number}'
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text())
assert set(m['exclusions'])=={'finalmanifest.json','verification-receipt.json'}
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['exclusions'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h
bindings=json.loads((S/'scientific-bindings.json').read_text())
if isinstance(bindings,dict):bindings=bindings['records']
def originals():
 for r in bindings:assert sha(r['original'])==sha(S/r['copy'])==r['sha256'],r
originals();refs=[];drift=[]
index_name='reference-bindings.json' if number==210 else 'index-bindings.json'
for r in json.loads((S/index_name).read_text()):
 p=Path(r['path']) if 'path' in r else S/r['copy']
 assert sha(p)==r['sha256'];refs.append(dict(path=str(p),sha256=r['sha256']))
hist=alias=0
for name in [('history.json' if number==210 else 'qualified-original-index.json'),'alias-refresh.json']:
 for r in json.loads((S/name).read_text())['records']:
  if r.get('missing'):continue
  p=Path(r['snapshot_reference']);assert sha(p)==r['sha256'];refs.append(dict(path=str(p),sha256=r['sha256']))
  orig=Path(r['original'])
  if not orig.exists() or sha(orig)!=r['sha256']:drift.append(str(orig))
  if name=='alias-refresh.json':alias+=1
  else:hist+=1
(P/'snapshot-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
shutil.copyfile(S/'checks.py',P/'checks.py')
q=subprocess.run([sys.executable,str(P/'checks.py')],capture_output=True,check=True)
(P/'checks.json').write_bytes(q.stdout);(P/'checks.stderr').write_bytes(q.stderr)
assert q.stdout==(S/'checks.json').read_bytes() and q.stderr==(S/'checks.stderr').read_bytes()
originals()
for r in refs:assert sha(r['path'])==r['sha256']
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),scientific_bindings=len(bindings),history_snapshots=hist,alias_snapshots=alias,external_references=len(refs),live_snapshot_drift=drift,frozen_files=len(freeze),private_replay='byte-identical',qualification='Finite exact controls and input integrity only; no universal reconstruction or factorial separation theorem. Source and current-prior gaps preserved.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
