import urllib.request,urllib.error,json,hashlib,datetime,sys
from pathlib import Path
label,url=sys.argv[1:];r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retries':0}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical source review'}),timeout=25) as f:
  data=f.read(15000000);r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());Path('sources/'+label).write_bytes(data)
except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
Path('receipts/http-'+label+'.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
