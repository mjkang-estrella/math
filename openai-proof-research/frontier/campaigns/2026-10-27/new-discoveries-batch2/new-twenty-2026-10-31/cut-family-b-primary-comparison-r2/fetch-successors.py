import os,resource,requests,hashlib,json,datetime,time,concurrent.futures
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(60,60))
o=Path(__file__).parent
urls={"ddlp-citers":"https://api.openalex.org/works?filter=cites:W3025166574&per-page=100","saliquant":"https://www.dmlett.com/archive/v12/DML23_v12_pp209-216.pdf","oooooob":"https://arxiv.org/pdf/2605.23213","transfer":"https://arxiv.org/pdf/2602.14325"}
def fetch(z):
 name,url=z;t=time.monotonic();r={"name":name,"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  x=requests.get(url,timeout=(12,48),headers={"User-Agent":"Mathematical-source-review/1.0"});data=x.content;assert len(data)<=20*1024**2;r.update(status=x.status_code,final_url=x.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(o/(name+('.pdf' if name=='published' and data.startswith(b'%PDF') else '.body'))).write_bytes(data)
 except Exception as e:r['error']=str(e)
 r['elapsed_seconds']=time.monotonic()-t;return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: rows=list(ex.map(fetch,urls.items()))
(o/'http-successors.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
