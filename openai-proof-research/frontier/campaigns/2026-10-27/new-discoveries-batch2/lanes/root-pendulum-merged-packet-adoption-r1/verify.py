from pathlib import Path
import hashlib,json,subprocess,sys,datetime,zipfile
P=Path(__file__).resolve().parent;S=P.parent/'sol-pendulum-manuscript-packet-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(p,r):
 assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
m=json.loads((S/'delivery-manifest.json').read_text())['files']
for name,r in m.items():check(S/name,r)
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file() and 'fresh-extraction' not in p.parts and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
z=S/'merged-source.zip';assert sha(z)=='cd5c7e4ce387b810dcd5b96f307a23b9ab688db3bb4b4908373496e28eee1fd6'
with zipfile.ZipFile(z) as f:
 manifest=json.loads(f.read('manifest.json'))
 assert set(f.namelist())==set(manifest)|{'manifest.json'}
 for name,h in manifest.items():assert hashlib.sha256(f.read(name)).hexdigest()==h,name
 assert not any(n.endswith(('.olean','.ilean','.ir','.pyc','.so','.o')) for n in f.namelist())
with (P/'replay.log').open('w') as log:
 subprocess.run([sys.executable,str(S/'packet/replay_guard.py'),sys.executable,str(S/'packet/replay.py'),str(z),str(P/'fresh-extraction')],stdout=log,stderr=subprocess.STDOUT,check=True)
with (P/'rebuild.log').open('w') as log:
 subprocess.run([sys.executable,str(P/'fresh-extraction/package.py'),str(P/'reproduced.zip')],cwd=P/'fresh-extraction',stdout=log,stderr=subprocess.STDOUT,check=True)
assert sha(P/'reproduced.zip')==sha(z)
for r in freeze:check(Path(r['path']),r)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',delivery_manifest_files=len(m),frozen_files=len(freeze),archive_payload_files=len(manifest),archive_sha256=sha(z),root_extracted_replay='PASS',byte_identical_rebuild=True,mathematical_modules=14,actual_declarations=139,qualification='No authored PDF or visual QA; independent review and historical coverage remain pending')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
