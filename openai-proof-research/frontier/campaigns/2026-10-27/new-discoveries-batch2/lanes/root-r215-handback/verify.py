from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r215'
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'manifest.json').read_text())
assert set(m['explicit_exclusions'])=={'manifest.json','verification-receipt.json'}
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['explicit_exclusions'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h
bindings=json.loads((S/'bindings.json').read_text());sci=json.loads((S/'scientific-freeze.json').read_text())
def originals():
 for r in bindings:
  assert sha(S/r['copy'])==r['sha256']
  if r['kind']!='administrative snapshot only':assert sha(r['original'])==r['sha256']
 for r in sci:assert sha(S/r['original'])==sha(S/r['copy'])==r['sha256']
originals();refs=[]
for name in ['qualified-original-index.json','alias-refresh.json']:
 for r in json.loads((S/name).read_text())['records']:
  p=Path(r['snapshot_reference']);assert sha(p)==r['sha256'];refs.append(dict(path=str(p),sha256=r['sha256']))
(P/'snapshot-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
for name in ['projection','closest']:
 q=subprocess.run(['pdftotext','-layout',str(S/'frozen'/(name+'.pdf')),'-'],capture_output=True,check=True)
 assert q.stdout==(S/(name+'.txt')).read_bytes()
shutil.copyfile(S/'checks.py',P/'checks.py')
q=subprocess.run([sys.executable,str(P/'checks.py')],capture_output=True,check=True)
(P/'checks.json').write_bytes(q.stdout);(P/'checks.stderr').write_bytes(q.stderr)
assert json.loads(q.stdout)==json.loads((S/'check-results.json').read_text())
originals()
for r in refs:assert sha(r['path'])==r['sha256']
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),assigned_bindings=len(bindings),scientific_pairs=len(sci),historical_references=len(refs),frozen_files=len(freeze),private_replay='exact JSON equality',extraction_replay='byte-identical',qualification='Supporting rational controls only; universal column packing and distance inequality remain open. Administrative drift and failed checks preserved.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
