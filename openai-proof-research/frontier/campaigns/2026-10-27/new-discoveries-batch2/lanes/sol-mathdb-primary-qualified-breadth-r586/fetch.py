from pathlib import Path
import urllib.request,json,hashlib,datetime
D=Path(__file__).parent;out=[]
for n,u in [('owr1592.html','https://ems.press/journals/owr/articles/1592'),('coloring1103.5849v1.pdf','https://arxiv.org/pdf/1103.5849v1')]:
 x={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=35) as r:b=r.read();x['final_url']=r.url
  (D/n).write_bytes(b);x.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:x['failure']=str(e)
 out.append(x)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
