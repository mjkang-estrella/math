from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r212'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'manifest.json').read_text())
assert set(m['excluded'])=={'manifest.json','verification-receipt.json'}
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['excluded'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h
bindings=json.loads((S/'bindings.json').read_text())
def originals():
 for r in bindings:assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256']
 for r in map(json.loads,(S/'http.jsonl').read_text().splitlines()):
  if 'sha256' in r:assert sha(S/'sources'/r['name'])==sha(S/'frozen'/r['name'])==r['sha256']
  if 'failure_sha256' in r:assert sha(S/'failures'/(r['name']+'.body'))==r['failure_sha256']
originals();refs=[]
for name in ['qualified-original-index.json','alias-refresh.json']:
 for r in json.loads((S/name).read_text())['records']:
  p=Path(r['snapshot_reference']);assert sha(p)==r['sha256'];refs.append(dict(path=str(p),sha256=r['sha256']))
(P/'snapshot-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
for name in ['karam','lim']:
 q=subprocess.run(['pdftotext','-layout',str(S/'frozen'/(name+'.pdf')),'-'],capture_output=True,check=True)
 assert q.stdout==(S/(name+'.txt')).read_bytes()
 assert q.stderr==(S/'receipts'/(name+'.extract.stderr')).read_bytes()
shutil.copyfile(S/'checks.py',P/'checks.py')
q=subprocess.run([sys.executable,str(P/'checks.py')],capture_output=True,check=True)
(P/'checks.stdout').write_bytes(q.stdout);(P/'checks.stderr').write_bytes(q.stderr)
assert q.stdout==(S/'receipts/checks.stdout').read_bytes() and q.stderr==(S/'receipts/checks.stderr').read_bytes()
originals()
for r in refs:assert sha(Path(r['path']))==r['sha256']
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),assigned_bindings=len(bindings),historical_references=len(refs),frozen_files=len(freeze),private_replay='byte-identical',extraction_replay='byte-identical',qualification='Finite metric-graph controls and all-vertices route obstruction only; no uniform common-center theorem. Access and workflow gaps preserved.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
