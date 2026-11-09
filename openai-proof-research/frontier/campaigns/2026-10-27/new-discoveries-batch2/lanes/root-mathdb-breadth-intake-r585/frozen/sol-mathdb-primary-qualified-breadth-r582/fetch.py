from pathlib import Path
import urllib.request,json,hashlib,datetime
D=Path(__file__).parent
routes=[('owr736.html','https://ems.press/journals/owr/articles/736'),('owr711.html','https://ems.press/journals/owr/articles/711'),('fano1804.07673v2.pdf','https://arxiv.org/pdf/1804.07673v2'),('rudin04a.pdf','https://www.jmlr.org/papers/volume5/rudin04a/rudin04a.pdf')]
out=[]
for name,url in routes:
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();x.update(status=r.status,final_url=r.url)
  (D/name).write_bytes(b);x.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:x['error']=str(e)
 out.append(x)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
