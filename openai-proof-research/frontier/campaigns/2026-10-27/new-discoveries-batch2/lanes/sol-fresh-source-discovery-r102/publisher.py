from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
P=Path(__file__).resolve().parent;log=json.loads((P/'http.json').read_text())
urls={'original-publisher.html':'https://www.sciencedirect.com/science/article/pii/S0166218X26003732'}
for n,u in urls.items():
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read();s=r.status
  (P/'sources'/n).write_bytes(b);log.append(dict(url=u,status=s,file='sources/'+n,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));print(n,s,len(b),flush=True)
 except Exception as e:log.append(dict(url=u,error=str(e)));print(n,str(e),flush=True)
 (P/'http.json').write_text(json.dumps(log,indent=2))
