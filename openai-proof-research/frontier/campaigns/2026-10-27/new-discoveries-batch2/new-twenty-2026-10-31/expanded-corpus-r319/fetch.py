import os,resource,time,json,hashlib,urllib.request,concurrent.futures
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(110,110)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).parent; start=time.time()
urls=json.loads((p/'fetch-urls.json').read_text())
def get(pair):
 name,url=pair; t=time.time(); rec={'name':name,'url':url,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'read_depth':'retrieved only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=12) as r:
   b=r.read(6000001); assert len(b)<=6000000; rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),headers=dict(r.headers)); (p/name).write_bytes(b)
 except Exception as e: rec['error']=str(e)
 rec['wall_seconds']=time.time()-t; return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: receipts=list(ex.map(get,urls))
(p/('http-receipts-'+str(int(start))+'.json')).write_text(json.dumps(receipts,indent=2))
print(json.dumps([{k:v for k,v in r.items() if k!='headers'} for r in receipts],indent=2))
print('RESOURCE',json.dumps({'wall':time.time()-start,'affinity':list(os.sched_getaffinity(0)),'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'cpu':resource.getrusage(resource.RUSAGE_SELF).ru_utime+resource.getrusage(resource.RUSAGE_SELF).ru_stime}))
