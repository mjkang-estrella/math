from pathlib import Path
import urllib.request,urllib.error,json,hashlib,re
O=Path(__file__).parent; (O/'primary').mkdir(exist_ok=True)
log=[]
for name,url in [('4133.html','https://ems.press/journals/owr/articles/4133'),('4426.html','https://ems.press/journals/owr/articles/4426'),('4411.html','https://ems.press/journals/owr/articles/4411'),('1210.0206v3.pdf','https://arxiv.org/pdf/1210.0206v3')]:
 try:
  with urllib.request.urlopen(url,timeout=30) as r:b=r.read(8000000);status=r.status
  (O/'primary'/name).write_bytes(b);log.append({'url':url,'file':'primary/'+name,'status':status,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
  if name.endswith('html'):print(name,re.findall(r'href="([^"]+(?:pdf|serial-article-files)[^"]*)"',b.decode()))
 except Exception as e:log.append({'url':url,'failure':repr(e),'retry':False});print(name,repr(e))
(O/'downloads.json').write_text(json.dumps(log,indent=2)+'\n')
