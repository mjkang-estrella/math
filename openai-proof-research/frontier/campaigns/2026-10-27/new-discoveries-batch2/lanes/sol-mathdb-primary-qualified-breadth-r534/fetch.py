from pathlib import Path
import urllib.request,hashlib,json,datetime
D=Path(__file__).parent;out=[]
for v in ['2602.15754v1','2603.16304v1','2603.08123v1','2602.14931v1']:
 url='https://arxiv.org/html/'+v;t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read();status=r.status
  p=D/(v+'.html');p.write_bytes(b);out.append(dict(url=url,utc=t,path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),status=status))
 except Exception as e:out.append(dict(url=url,utc=t,error=str(e)))
(D/'retrieval-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
