from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r200';R=S.parents[5]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text());excluded=m.get('excludes',m.get('exclusions'))
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(excluded)==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h,n
if S.name.endswith('197'):
 rows=json.loads((S/'input-bindings.json').read_text())+json.loads((S/'scientific-input-freeze.json').read_text())['bindings']
else:
 rows=[(r['original'],r['copy'],r['sha256'],None) for r in json.loads((S/'scientific-freeze.json').read_text())+json.loads((S/'primary-freeze.json').read_text())]
def originals():
 for n,c,h,z in rows:
  a=Path(n);a=a if a.is_absolute() else R/a
  for p in [a,S/c]:assert sha(p)==h and (z is None or p.stat().st_size==z),str(p)
originals();shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
if S.name.endswith('197'):
 a=json.loads((P/'checks.json').read_text());b=json.loads((S/'checks.json').read_text());a.pop('utc');b.pop('utc');assert a==b
 replay='scientific JSON identical excluding actual run UTC'
else:
 assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes();replay='byte-identical'
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),scientific_original_copy_pairs=len(rows),frozen_files=len(freeze),private_replay=replay,qualification='Method diagnostics only; universal source endpoint remains unresolved. First-read freezing deviation preserved; final-freeze integrity only.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
