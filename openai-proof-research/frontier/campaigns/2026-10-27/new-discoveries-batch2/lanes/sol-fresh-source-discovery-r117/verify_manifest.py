import json,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
n=0
with (L/'finalmanifest.jsonl').open() as f:
 for s in f:
  d=json.loads(s);p=L/d['path'];h=hashlib.sha256()
  with p.open('rb') as inp:
   for b in iter(lambda:inp.read(262144),b''):h.update(b)
  assert h.hexdigest()==d['sha256'],str(p)
  assert p.stat().st_size==d['bytes'],str(p)
  n+=1
print(json.dumps({'status':'PASS','manifest_entries_verified':n}))
