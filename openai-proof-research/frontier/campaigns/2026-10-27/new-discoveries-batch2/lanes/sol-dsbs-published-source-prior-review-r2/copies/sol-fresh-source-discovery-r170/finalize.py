import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def records(excluded):
 out=[]
 for p in sorted(L.rglob('*')):
  if p.is_file() and str(p.relative_to(L)) not in excluded:
   b=p.read_bytes();out.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
 return out
ex={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
j=dict(utc=now(),policy='All lane payload files; scientific-freeze/finalmanifest/self-mutating verification receipt excluded explicitly',records=records(ex))
(L/'scientific-freeze.json').write_text(json.dumps(j,indent=2)+'\n')
k=dict(utc=now(),policy='All lane payload plus scientific-freeze; finalmanifest self and self-mutating verification receipt excluded explicitly',records=records({'finalmanifest.json','manifest-verification.json'}))
(L/'finalmanifest.json').write_text(json.dumps(k,indent=2)+'\n')
print(len(j['records']),len(k['records']))
