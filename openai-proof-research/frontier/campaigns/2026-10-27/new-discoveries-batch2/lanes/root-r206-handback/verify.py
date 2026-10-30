from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r206'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'manifest.json').read_text())
assert set(m['exclusions'])=={'manifest.json','verification-receipt.json'}
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['exclusions'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h
b=json.loads((S/'scientific-bindings.json').read_text())
def originals():
 for r in b['primary']:assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256']
 g=b['guard'];assert sha(Path(g['original']))==sha(S/g['copy'])==g['sha256']
originals();refs=[]
history=json.loads((S/'historical-after.json').read_text())['records']
for r in history:
 p=Path(r['snapshot']);p=p if p.is_absolute() else S/p
 assert sha(p)==r['expected']==r['snapshot_sha256'];refs.append(dict(path=str(p),sha256=r['expected']))
aliases=json.loads((S/'alias-screen.json').read_text())['records']
for r in aliases:
 if not r.get('missing'):
  p=Path(r['snapshot']);assert sha(p)==r['sha256'];refs.append(dict(path=str(p),sha256=r['sha256']))
for r in json.loads((S/'assigned-bindings.json').read_text()):assert sha(S/r['copy'])==r['sha256']
(P/'snapshot-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
shutil.copyfile(S/'check.py',P/'check.py')
with (P/'checker-output.json').open('w') as f:subprocess.run([sys.executable,str(P/'check.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
c=json.loads((P/'checks.json').read_text())
for g in c['graphs']:
 if g['n']<=6:assert g['dfs_steps']<=200000
 ds=g.get('witness',[]);n=g['n']
 if ds:
  assert len(set(map(tuple,ds)))==len(ds)
  assert all(len(d)==n and min(d)>=1 and max(d)<=n for d in ds)
  assert all(sum(x>y for x in ds[i] for y in ds[(i+1)%len(ds)])==n*n//2+1 for i in range(len(ds)))
originals()
for r in refs:assert sha(Path(r['path']))==r['sha256']
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),scientific_pairs=len(b['primary']),history_snapshots=len(history),alias_snapshots=len(aliases),frozen_files=len(freeze),private_replay='byte-identical',qualification='Finite exact graph and padding controls only; no universal long-cycle construction. Existing workflow qualifications preserved.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
