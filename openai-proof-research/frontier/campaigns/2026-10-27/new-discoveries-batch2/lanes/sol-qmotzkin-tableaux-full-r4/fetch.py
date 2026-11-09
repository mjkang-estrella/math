import urllib.request, json, hashlib, datetime
from pathlib import Path
p=Path(__file__).resolve().parent
receipts=[]
for name,url in [('wachs.pdf','https://www.math.miami.edu/~wachs/papers/flagged.pdf'),('kumar.html','https://arxiv.org/html/2306.10289v1'),('source.html','https://arxiv.org/html/1805.00113v1')]:
 r={'file':'sources/'+name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f: data=f.read(); r['status']=f.status
  (p/'sources'/name).write_bytes(data); r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:r['error']=str(e)
 receipts.append(r)
(p/'retrievals.json').write_text(json.dumps(receipts,indent=2)+'\n')
