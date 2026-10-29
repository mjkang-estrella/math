import urllib.request,urllib.error,hashlib,json,time,sys
from pathlib import Path
L=Path(__file__).resolve().parent
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 rec={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'url':url,'path':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=35) as r:
   b=r.read(12000000);rec.update(status=r.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),final_url=r.url);(L/'sources'/name).write_bytes(b)
 except Exception as e:
  rec.update(error=str(e),status=getattr(e,'code',None))
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
 if rec.get('status') in (403,429):break
