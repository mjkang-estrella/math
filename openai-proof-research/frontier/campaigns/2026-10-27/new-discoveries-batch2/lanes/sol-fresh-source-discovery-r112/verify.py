from pathlib import Path
import hashlib,json
L=Path(__file__).parent;n=0
with (L/'manifest.jsonl').open() as f:
 for line in f:
  row=json.loads(line);h=hashlib.sha256();size=0
  with (L/row['path']).open('rb') as inp:
   while b:=inp.read(1048576):h.update(b);size+=len(b)
  assert size==row['bytes'] and h.hexdigest()==row['sha256'],row['path']
  print(json.dumps({'path':row['path'],'verified':True}),flush=True);n+=1
print(json.dumps({'verified_entries':n,'status':'PASS','method':'JSONL manifest rows and1MiB streaming file reads; no aggregate content buffers'}))
