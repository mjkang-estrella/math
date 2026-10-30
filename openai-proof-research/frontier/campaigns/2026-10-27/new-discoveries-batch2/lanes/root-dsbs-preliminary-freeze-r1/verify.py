from pathlib import Path
import hashlib,json,shutil,subprocess,sys,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r170'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(p,r):assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
frozen=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'files':frozen},indent=2)+'\n')
science=json.loads((S/'scientific-freeze.json').read_text());manifest=json.loads((S/'finalmanifest.json').read_text())
for obj in [science,manifest]:
 for r in obj['records']:check(S/r['path'],r)
pv=json.loads((S/'provenance.json').read_text());assert sha(Path(pv['guard']['path']))==pv['guard']['sha256']
for r in pv['http_records']:
 if r.get('status')==200:assert sha(S/'sources'/r['name'])==r['sha256']
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.log').open('w') as log:subprocess.run([sys.executable,str(P/'checks.py')],stdout=log,stderr=subprocess.STDOUT,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
t=(S/'sources/dsbs-clean.txt').read_text();sections=[]
for marker,size in [('Conjecture 1',1800),('Proposition 1',2100),('IV-A Converse',2000)]:
 starts=[];start=0
 while True:
  pos=t.find(marker,start)
  if pos<0:break
  starts.append(pos);start=pos+len(marker)
 sections.extend(t[max(0,pos-150):pos+size] for pos in starts)
(P/'source-excerpts.txt').write_text('\n\n'.join(sections)+'\n')
for r in frozen:check(Path(r['path']),r)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',scientific_records=len(science['records']),manifest_records=len(manifest['records']),frozen_originals=len(frozen),diagnostic_replay='byte-identical private copy',qualification='High-precision and floating-point diagnostics, not exact arithmetic certification; no independent eligibility or universal mathematical PASS')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
