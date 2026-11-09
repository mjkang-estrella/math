import os,resource,pathlib,json,urllib.request,urllib.error,hashlib,time,concurrent.futures,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
l=pathlib.Path(__file__).parent;(l/'http').mkdir(exist_ok=True)
def fetch(job):
 name,url=job;r={'url':url,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'read_depth':'retrieved_only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source qualification'}),timeout=22) as f:
   data=f.read(24000000);r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(l/'http'/name).write_bytes(data)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 (l/'http'/(name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');print(name,r.get('status'),r.get('bytes'),r.get('error',''),flush=True)
jobs=json.loads((l/sys.argv[1]).read_text())
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(fetch,jobs))
