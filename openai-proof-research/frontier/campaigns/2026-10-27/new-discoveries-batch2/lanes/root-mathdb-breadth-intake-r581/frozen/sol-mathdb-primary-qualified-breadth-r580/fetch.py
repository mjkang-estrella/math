from pathlib import Path
import urllib.request,hashlib,json,datetime
D=Path(__file__).parent;u='https://arxiv.org/html/2512.16062v2';out=[]
try:
 with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research statement screening'}),timeout=40) as r:
  b=r.read(); p=D/'2512.16062v2.html';p.write_bytes(b);out.append(dict(url=u,final_url=r.url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),status=r.status))
except Exception as e:out.append(dict(url=u,error=str(e),retry=False))
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
