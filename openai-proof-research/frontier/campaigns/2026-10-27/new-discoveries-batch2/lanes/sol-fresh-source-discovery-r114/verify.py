import json,hashlib
from pathlib import Path
O=Path(__file__).parent
def digest(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  while b:=f.read(262144):h.update(b)
 return h.hexdigest()
n=0
with open(O/'manifest.jsonl') as f:
 for line in f:
  r=json.loads(line);p=O/r['path']
  assert p.stat().st_size==r['bytes'],str(p)
  assert digest(p)==r['sha256'],str(p)
  n+=1
print(json.dumps({'verified_files':n,'manifest_sha256':digest(O/'manifest.jsonl'),'status':'PASS'}))
