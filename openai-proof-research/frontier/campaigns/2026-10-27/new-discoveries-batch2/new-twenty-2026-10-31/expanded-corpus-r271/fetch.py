import requests,resource,json,hashlib,time,sys,concurrent.futures
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
def fetch(url):
 key=hashlib.sha256(url.encode()).hexdigest()[:16];d={'url':url,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
 try:
  r=requests.get(url,timeout=12);d.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content));ext='.pdf' if r.content.startswith(b'%PDF') else '.html';f=p/'sources'/(key+ext);f.write_bytes(r.content);d['file']=str(f)
 except Exception as e:d['error']=str(e)
 (p/'sources'/(key+'.receipt.json')).write_text(json.dumps(d,indent=2));return d
if __name__=='__main__':
 urls=sys.argv[1:]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
  for r in ex.map(fetch,urls):print(json.dumps(r))
