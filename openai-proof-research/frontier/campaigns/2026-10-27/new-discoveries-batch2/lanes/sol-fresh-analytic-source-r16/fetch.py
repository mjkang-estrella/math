from pathlib import Path
import urllib.request,hashlib,json,datetime
root=Path(__file__).resolve().parent
items=[]
for name,url in [('means-v2.html','https://arxiv.org/html/2405.13618v2'),('means-abs.html','https://arxiv.org/abs/2405.13618'),('means-v1.html','https://arxiv.org/html/2405.13618v1')]:
 r={'url':url,'file':'sources/'+name,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f: data=f.read();r['status']=f.status
  (root/r['file']).write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
 except Exception as e:r['error']=str(e)
 items.append(r)
(root/'retrievals.json').write_text(json.dumps(items,indent=2))
