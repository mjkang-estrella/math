import sys,json,hashlib,datetime,urllib.request
from pathlib import Path
L=Path(__file__).resolve().parent
url,name=sys.argv[1:]; p=L/'sources'/name
r={'url':url,'accessed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'}),timeout=35) as f:
  b=f.read(12000001)
  if len(b)>12000000:raise ValueError('12MB response cap')
  p.write_bytes(b);r.update(status=f.status,final_url=f.url,headers=dict(f.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),path=str(p.relative_to(L)))
except Exception as e:r['error']=str(e)
(L/'sources'/(name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');print(r)
