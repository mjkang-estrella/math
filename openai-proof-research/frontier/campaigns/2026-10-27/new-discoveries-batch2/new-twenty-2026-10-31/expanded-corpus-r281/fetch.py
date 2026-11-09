from pathlib import Path
import urllib.request,urllib.error,json,datetime,hashlib,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent; (p/'sources').mkdir(exist_ok=True)
rows=json.loads((p/'reservation.json').read_text())['rows']; urls=list(dict.fromkeys(r['source_url'] for r in rows))
def fetch(url):
 name=hashlib.sha256(url.encode()).hexdigest()[:16]; out={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0 (public source review)'}),timeout=12) as r:
   b=r.read(16000000);out.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),content_type=r.headers.get('Content-Type'));(p/out['file']).write_bytes(b)
 except Exception as e:out.update(error=str(e),status=getattr(e,'code',None))
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 receipts=list(ex.map(fetch,urls))
(p/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
for x in receipts:print(json.dumps(x))
