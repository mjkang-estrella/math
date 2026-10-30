from pathlib import Path
import json,hashlib,subprocess,sys,datetime
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.loads((L/'scientific-freeze.json').read_text())
for r in a['files']:
 p=L/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
for r in a['external_fixed_inputs']:
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
before=(L/'checks.json').read_bytes()
subprocess.run([sys.executable,str(L/'checks.py')],check=True,stdout=subprocess.DEVNULL)
assert (L/'checks.json').read_bytes()==before,'diagnostic replay bytes changed'
m=json.loads((L/'finalmanifest.json').read_text())
for r in m['files']:
 p=L/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
rec=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',scientific_files=len(a['files']),external_fixed_inputs=len(a['external_fixed_inputs']),manifest_files=len(m['files']),diagnostic_replay='byte-identical',scope='integrity and bounded diagnostics; not source-proof or novelty clearance',manifest_sha256=sha(L/'finalmanifest.json'))
(L/'manifest-verification.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
