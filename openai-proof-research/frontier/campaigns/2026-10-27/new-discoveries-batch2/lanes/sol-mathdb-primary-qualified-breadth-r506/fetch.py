from pathlib import Path
import urllib.request,datetime,json,hashlib
O=Path(__file__).parent;(O/'sources').mkdir(exist_ok=True);log=[]
for a in ['2502.00134','2604.02404','2609.02334','2609.11719','2609.18539','2609.20071','1612.05818','2308.05868']:
 url='https://arxiv.org/html/'+a
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as r:
   b=r.read();e.update(status=r.status,final_url=r.url)
  p=O/'sources'/ (a+'.html');p.write_bytes(b);e.update(path=str(p.resolve()),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as x:e['error']=str(x)
 log.append(e);(O/'source-bindings.json').write_text(json.dumps(log,indent=2)+'\n');print(e)
