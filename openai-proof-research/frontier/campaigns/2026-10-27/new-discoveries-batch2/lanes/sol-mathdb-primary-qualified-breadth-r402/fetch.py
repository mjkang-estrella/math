from pathlib import Path
import urllib.request,urllib.error,datetime,hashlib,json
O=Path(__file__).resolve().parent/'primary';O.mkdir(exist_ok=True)
urls=[('fi','https://math.uchicago.edu/~farb/papers/FImod.pdf'),('edge','https://msp.org/gt/2020/24-1/gt-v24-n1-p07-p.pdf'),('aj','https://www.impan.pl/shop/publication/transaction/download/product/91725')]
for name,url in urls:
 meta={'url':url,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'exact bytes at URL; publication correspondence to be checked in body','attempts':1}
 try:
  with urllib.request.urlopen(url,timeout=35) as r:
   b=r.read(12*1024*1024+1);assert len(b)<=12*1024*1024;meta.update(final_url=r.url,status=r.status,size=len(b),sha256=hashlib.sha256(b).hexdigest(),content_type=r.headers.get('Content-Type'))
  assert b.startswith(b'%PDF'), 'not PDF; stop'
  (O/(name+'.pdf')).write_bytes(b)
 except Exception as e:meta['failure']=repr(e)
 (O/(name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n'); print(json.dumps(meta))
