from pathlib import Path
import urllib.request,datetime,hashlib,json,sys
D=Path(__file__).resolve().parents[1]
name,url=sys.argv[1:]
r=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
assert not (D/'receipts'/f'http-{name}.json').exists()
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical review'}),timeout=25) as q:
  b=q.read(40000000);(D/'outputs'/name).write_bytes(b);r.update(status=q.status,final_url=q.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
except Exception as e:r.update(error=str(e),status=getattr(e,'code',None),not_retried=True)
(D/'receipts'/f'http-{name}.json').write_text(json.dumps(r,indent=2));print(r)
