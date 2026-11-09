import urllib.request,datetime,json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parent;out=[]
# Fixed small body screen, no retries or alternate routes after failures.
for name,url in [('defant-zheng','https://arxiv.org/html/2008.12297'),('yi','https://arxiv.org/html/2604.18626v1'),('history-current','https://arxiv.org/abs/2410.17057')]:
 r=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  p=D/(name+'.html');p.write_bytes(b);r.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r.update(error=str(e),retry=False)
 out.append(r)
(D/'http-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
