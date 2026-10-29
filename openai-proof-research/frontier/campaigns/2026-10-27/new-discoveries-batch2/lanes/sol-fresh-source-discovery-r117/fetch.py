import urllib.request,hashlib,json,time,sys
from pathlib import Path
L=Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 rcp={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'url':url,'path':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Source-research/1.0'}),timeout=25) as r:
   b=r.read(8000001)
   if len(b)>8000000:raise ValueError('8MB bound reached')
   (L/'sources'/name).write_bytes(b);rcp.update(status=r.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),final_url=r.url)
 except Exception as e:rcp.update(error=str(e),status=getattr(e,'code',None))
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rcp)+'\n')
 print(json.dumps(rcp))
 if rcp.get('status') in (403,429):break
