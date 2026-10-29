from pathlib import Path
import json,urllib.request,hashlib,re
P=Path(__file__).resolve().parent
log=json.loads((P/'http.json').read_text());head=json.loads((P/'sources/omega_head.json').read_text())['sha']
u='https://api.github.com/repos/the-omega-institute/trureturing/compare/1b999d9fda71df7537b62327147496d64a6f66ef...'+head
try:
 with urllib.request.urlopen(u,timeout=25) as r:b=r.read()
 f=P/'sources/omega-full-delta.json';f.write_bytes(b);log.append(dict(url=u,status=200,file=str(f.relative_to(P)),sha256=hashlib.sha256(b).hexdigest()))
 d=json.loads(b);print('baseline to live',d.get('total_commits'),len(d.get('files',[])))
 for i,r in enumerate(d.get('files',[])):
  if r['status']=='removed':continue
  u='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+r['filename']
  try:
   with urllib.request.urlopen(u,timeout=20) as rr:b=rr.read()
   f=P/'sources'/('omega-full-delta-body-'+str(i)+'.txt');f.write_bytes(b);log.append(dict(url=u,status=200,file=str(f.relative_to(P)),sha256=hashlib.sha256(b).hexdigest()))
   print(r['filename'],len(b))
  except Exception as e:log.append(dict(url=u,error=str(e)))
except Exception as e:log.append(dict(url=u,error=str(e)))
(P/'http.json').write_text(json.dumps(log,indent=2))
