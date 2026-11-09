import urllib.request, json, hashlib, datetime
from pathlib import Path
P=Path(__file__).parent
jobs=[('hong.pdf','https://arxiv.org/pdf/2108.00326v1'),('fodor-published.pdf','https://publicatio.bibl.u-szeged.hu/39648/1/1-s2.0-S0012365X26001111.pdf')]
r=[]
for name,url in jobs:
 e={'file':'sources/'+name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as q: b=q.read(); e['status']=q.status
  (P/e['file']).write_bytes(b);e.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as x:e['error']=str(x)
 r.append(e)
(P/'retrievals-3.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r,indent=2))
