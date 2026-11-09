import urllib.request,json,hashlib,datetime
from pathlib import Path
base=Path(__file__).parent
items=[('cascade-source.pdf','https://pouyanne.perso.math.cnrs.fr/ccnppArxivAvr20.pdf'),('cascade-abs.html','https://arxiv.org/abs/2004.07893'),('age-source.html','https://arxiv.org/html/2104.08050v3')]
r=[]
for name,url in items:
 a={'file':'sources/'+name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f: data=f.read();a['status']=f.status
  (base/'sources'/name).write_bytes(data);a.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:a['error']=str(e)
 r.append(a)
(base/'fetch-receipts.json').write_text(json.dumps(r,indent=2))
