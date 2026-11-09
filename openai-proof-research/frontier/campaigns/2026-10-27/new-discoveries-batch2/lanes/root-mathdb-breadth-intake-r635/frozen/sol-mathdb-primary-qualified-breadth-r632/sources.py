from pathlib import Path
import json,hashlib,urllib.request,datetime
from html.parser import HTMLParser
O=Path(__file__).resolve().parent;L=O.parent
flat=json.loads((O/'flat-bindings.json').read_text())
for p in (L/'sol-mathdb-primary-qualified-breadth-r414/primary').glob('dtuples*'):
 d=p.read_bytes();flat.append({'path':str(p),'size':len(d),'sha256':hashlib.sha256(d).hexdigest()})
(O/'flat-bindings.json').write_text(json.dumps(flat,indent=2)+'\n')
prov=[]
for name,url in [('waldschmidt','https://arxiv.org/html/math/0312440v1'),('automatic','https://arxiv.org/html/math/0511674v1'),('cover','https://arxiv.org/html/2109.01237v1')]:
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'})
  with urllib.request.urlopen(req,timeout=25) as r:d=r.read();final=r.url
  p=O/(name+'.html');p.write_bytes(d);prov.append({'name':name,'url':url,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'size':len(d),'sha256':hashlib.sha256(d).hexdigest(),'status':200})
 except Exception as e:prov.append({'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'failure':str(e),'retry':False})
 (O/'fetch-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print(json.dumps(prov))
