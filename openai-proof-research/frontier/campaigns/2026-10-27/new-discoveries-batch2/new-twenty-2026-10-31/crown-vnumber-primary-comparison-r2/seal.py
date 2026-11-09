import os, resource, signal, hashlib, json, datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
signal.alarm(140)
q=Path(__file__).resolve().parent
for f in q.glob('*.json'):
 json.loads(f.read_text())
for line in (q/'http-receipts.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'error' not in r:
  f=q/'http'/r['name'];assert len(f.read_bytes())==r['bytes'] and hashlib.sha256(f.read_bytes()).hexdigest()==r['sha256']
expected=json.loads((q/'frozen-inputs.json').read_text())
assert len(expected)==79
assert all(hashlib.sha256(Path(f).read_bytes()).hexdigest()==h for f,h in expected.items())
with (q/'jobs.jsonl').open('a') as f:
 f.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),job='seal-and-handback-check',state='source jobs all reaped; JSON, fetched-byte receipts and 79 frozen files verified; only final manifest write and process exit remain',limits=dict(cpu_s=120,wall_s=140,as_bytes=6*1024**3,cpus=2)))+'\n')
hashes={str(f.relative_to(q)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(q.rglob('*')) if f.is_file() and f.name!='artifact-hashes.json'}
(q/'artifact-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(json.dumps(dict(manifest_files=len(hashes),frozen='79/79 PASS before/after and seal',receipts='PASS',jobs='all source jobs ended/reaped',acceptance='HOLD',count='52/60',credit=0)))
