from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r193';R=S.parents[5]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n');counts={}
for name in ['scientific-input-freeze.json','scientific-freeze.json','finalmanifest.json']:
 j=json.loads((S/name).read_text())
 for n,h in j['files'].items():assert sha(S/n)==h,n
 if name=='finalmanifest.json':assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(j['excluded'])==set(j['files'])
 counts[name]=len(j['files'])
rows=json.loads((S/'history-receipt.json').read_text())['records']
for n,h,z in rows:
 for p in [R/n,S/'originals'/n]:assert sha(p)==h and p.stat().st_size==z,n
extra=json.loads((S/'additional-originals.json').read_text())
for r in extra:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=counts,historical_original_copy_pairs=len(rows),additional_original_copy_pairs=len(extra),frozen_files=len(freeze),private_replay='byte-identical',qualification='Finite regular-graph controls and local-method obstruction; universal extremal clique-forcing remains missing.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
