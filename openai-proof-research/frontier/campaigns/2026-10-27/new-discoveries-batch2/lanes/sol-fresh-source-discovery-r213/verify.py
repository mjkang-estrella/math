from pathlib import Path
import json,hashlib,subprocess,datetime,sys
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
checks=[]
for r in json.loads((L/'scientific-bindings.json').read_text())['records']:
 assert sha(Path(r['original']).read_bytes())==sha((L/r['copy']).read_bytes())==r['sha256'];checks.append(r['copy'])
refs=0;drift=[]
for name in ['qualified-original-index.json','alias-refresh.json']:
 for r in json.loads((L/name).read_text())['records']:
  if r.get('missing') and 'snapshot_reference' not in r:continue
  assert sha(Path(r['snapshot_reference']).read_bytes())==r['sha256'];refs+=1
  p=Path(r.get('original',r.get('reference_absolute')))
  if p.is_file() and sha(p.read_bytes())!=r['sha256']:drift.append(str(p))
for r in json.loads((L/'index-bindings.json').read_text()):assert sha(Path(r['path']).read_bytes())==r['sha256']
p=subprocess.run([sys.executable,str(L/'checks-bounded.py')],capture_output=True,timeout=80);assert p.returncode==0,p.stderr
assert json.loads(p.stdout)==json.loads((L/'checks-bounded.json').read_text())
for src,dst in [(n,n) for n in ['jacobi','gessel','lin','even','veto','kneser','bruhat','compression','counter']]:
 p=subprocess.run(['pdftotext','-layout',str(L/'frozen'/(src+'.pdf')),'-'],capture_output=True,timeout=20);assert p.returncode==0
 assert p.stdout==(L/(dst+'.txt')).read_bytes()
m=json.loads((L/'finalmanifest.json').read_text());assert set(m['exclusions'])=={'finalmanifest.json','verification-receipt.json'}
actual={str(p.relative_to(L)):sha(p.read_bytes()) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in m['exclusions']}
assert actual==m['files']
assert json.loads((L/'scouting.json').read_text())['screened']==16
assert len(json.loads((L/'retained-sources.json').read_text()))==4
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',scientific_bindings=len(checks),external_snapshot_references=refs,mutable_historical_drift=drift,checker_replay='PASS',text_reextraction='PASS',manifest_files=len(actual),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),exclusions=m['exclusions'])
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
