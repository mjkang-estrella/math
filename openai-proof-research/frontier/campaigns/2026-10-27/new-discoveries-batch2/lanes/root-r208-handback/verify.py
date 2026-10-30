from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r208'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text())
assert set(m['excluded'])=={'finalmanifest.json','verification-receipt.json'}
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['excluded'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h
rows=json.loads((S/'primary-freeze.json').read_text())+[json.loads((S/'guard-binding.json').read_text())]
def originals():
 for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
originals();refs=[];drift=[]
history=json.loads((S/'history-refresh.json').read_text())['records']
aliases=json.loads((S/'alias-refresh.json').read_text())['records']
for r in history+aliases:
 p=Path(r['canonical_copy']);assert sha(p)==r['sha256'];refs.append(dict(path=str(p),sha256=r['sha256']))
 orig=Path(r.get('original',r.get('reference_absolute')))
 if not orig.exists() or sha(orig)!=r.get('current_original_sha256',r['sha256']):drift.append(str(orig))
(P/'snapshot-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
c=json.loads((P/'checks.json').read_text());assert c['semigroups']==31378 and not c['subset_matching_failures']
originals()
for r in refs:assert sha(Path(r['path']))==r['sha256']
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),scientific_bindings=len(rows),history_snapshots=len(history),alias_snapshots=len(aliases),live_snapshot_drift=drift,frozen_files=len(freeze),private_replay='byte-identical',qualification='Finite semigroup and subset-matching controls only; no uniform Hall bound or full source resolution. Inherited failed threshold check and workflow limitations preserved.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
