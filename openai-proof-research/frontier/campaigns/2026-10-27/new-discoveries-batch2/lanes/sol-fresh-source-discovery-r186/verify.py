from pathlib import Path
import json,hashlib,sys,datetime,subprocess,os
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
mode=sys.argv[1]
name='scientific-freeze.json' if mode=='science' else 'finalmanifest.json'
j=json.loads((L/name).read_text());files=j['files'];actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(j['exclusions'])
assert set(files)==actual,(set(files)-actual,actual-set(files))
for p,r in files.items():
 b=(L/p).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'],p
report=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',checked=len(files),manifest=name,manifest_sha256=sha((L/name).read_bytes()),explicit_exclusions=j['exclusions'])
if mode=='science':
 copies=json.loads((L/'original-copy-provenance.json').read_text())['records'];root=L.parents[5];drift=[]
 for r in copies:
  assert sha((L/r['copy']).read_bytes())==r['sha256']
  if sha((root/r['original']).read_bytes())!=r['sha256']:drift.append(r['original'])
 report.update(copies_verified=len(copies),external_original_drift=drift)
 g=json.loads((L/'guard-binding.json').read_text());assert sha(Path(g['path']).read_bytes())==g['sha256']
 before=(L/'checks.json').read_bytes()
 env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
 p=subprocess.run(['python3',g['path'],'python3',str(L/'checks.py')],capture_output=True,env=env,timeout=230)
 assert p.returncode==0,(p.returncode,p.stderr.decode())
 assert before==(L/'checks.json').read_bytes()
 report.update(exact_replay='byte-identical PASS',replay_guard=json.loads(p.stderr.decode().strip().splitlines()[-1]),stdout_artifact_created=False)
out='scientific-verification.json' if mode=='science' else 'manifest-verification.json'
(L/out).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
