import urllib.request, json, hashlib, datetime
from pathlib import Path
P=Path(__file__).parent
jobs=[('vigh.html','https://arxiv.org/html/2610.08168v1'),('vigh-abs.html','https://arxiv.org/abs/2610.08168v1'),('reverse-araki.html','https://arxiv.org/html/2607.01263v1')]
r=[]
for name,url in jobs:
 e={'file':'sources/'+name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as q: b=q.read(); e['status']=q.status
  (P/e['file']).write_bytes(b);e.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as x:e['error']=str(x)
 r.append(e)
(P/'retrievals-2.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r,indent=2))
