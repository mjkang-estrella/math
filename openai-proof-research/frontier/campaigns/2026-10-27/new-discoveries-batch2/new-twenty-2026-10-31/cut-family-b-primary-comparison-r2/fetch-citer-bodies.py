import os,resource,requests,hashlib,json,datetime,time,concurrent.futures
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(60,60))
o=Path(__file__).parent
urls={"lctr":"https://arxiv.org/pdf/2207.05599v2","arithmetic":"https://math.colgate.edu/~integers/vb14/vb14.pdf","preprint-citers":"https://api.openalex.org/works?filter=cites:W4221164249&per-page=100"}
def fetch(z):
 name,url=z;t=time.monotonic();r={"name":name,"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  x=requests.get(url,timeout=(12,48),headers={"User-Agent":"Mathematical-source-review/1.0"});data=x.content;assert len(data)<=20*1024**2;r.update(status=x.status_code,final_url=x.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(o/(name+('.pdf' if name=='published' and data.startswith(b'%PDF') else '.body'))).write_bytes(data)
 except Exception as e:r['error']=str(e)
 r['elapsed_seconds']=time.monotonic()-t;return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: rows=list(ex.map(fetch,urls.items()))
(o/'http-citer-bodies.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
