from pathlib import Path
import urllib.request,datetime,hashlib,json
O=Path(__file__).resolve().parent;(O/'sources').mkdir(exist_ok=True);out=[]
for a in ['2506.17804','2504.20975','2504.19196','2506.16432']:
 url='https://arxiv.org/html/'+a+'v1';e={'url':url,'version':'v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read();e.update(status=r.status,content_type=r.headers.get('Content-Type'))
  p=O/'sources'/(a+'v1.html');p.write_bytes(b);e.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as ex:e.update(error=str(ex),disposition='HOLD; no retry')
 out.append(e)
(O/'source-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
