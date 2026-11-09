from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,sys
P=Path(__file__).resolve().parent; (P/'sources').mkdir(exist_ok=True)
name,url=sys.argv[1:];rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),method='urllib default TLS; one request; no access bypass')
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=25) as r:
  b=r.read(20000000);rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(P/'sources'/name).write_bytes(b)
except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
(P/'sources'/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
