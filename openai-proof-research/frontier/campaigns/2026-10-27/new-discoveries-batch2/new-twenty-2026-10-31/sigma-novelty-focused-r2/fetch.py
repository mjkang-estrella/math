import requests,hashlib,json,datetime,pathlib,sys,resource,os,concurrent.futures
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).parent
jobs=json.loads(sys.argv[1])
def fetch(j):
 name,url=j; rcp={'url':url,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=22,headers={'User-Agent':'Scholarly prior-art review (public access only)'})
  b=r.content;(p/'downloads'/name).write_bytes(b);rcp.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),content_type=r.headers.get('Content-Type'))
 except Exception as e:rcp.update(status=None,error=str(e))
 rcp['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(p/'receipts'/(name+'.json')).write_text(json.dumps(rcp,indent=2));return rcp
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,jobs):print(json.dumps(r))
