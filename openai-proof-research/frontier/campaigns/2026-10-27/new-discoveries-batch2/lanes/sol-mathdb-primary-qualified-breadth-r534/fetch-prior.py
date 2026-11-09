from pathlib import Path
import urllib.request,hashlib,json,datetime
D=Path(__file__).parent;url='https://arxiv.org/html/2412.05857v1';out={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=35) as r:b=r.read();out['status']=r.status
 p=D/'2412.05857v1.html';p.write_bytes(b);out.update(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest())
except Exception as e:out['error']=str(e)
(D/'prior-retrieval-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
