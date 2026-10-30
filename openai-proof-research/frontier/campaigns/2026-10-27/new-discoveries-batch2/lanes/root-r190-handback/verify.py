from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r190'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n');counts={}
for name in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((S/name).read_text())
 for n,h in j['files'].items():assert sha(S/n)==h,n
 if name=='finalmanifest.json':assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file() and p.name not in j['excludes']}==set(j['files'])
 counts[name]=len(j['files'])
pairs=[]
for name in ['original-copy-provenance.json','source-copy-provenance.json']:
 pairs.extend(json.loads((S/name).read_text()))
for r in pairs:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
g=json.loads((S/'provenance.json').read_text())['guard'];assert sha(Path(g['path']))==g['sha256']
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
for r in pairs:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=counts,original_copy_pairs=len(pairs),frozen_files=len(freeze),private_replay='byte-identical',qualification='Exact finite cosine diagnostics and reductions; no universal five-frequency lower bound.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
