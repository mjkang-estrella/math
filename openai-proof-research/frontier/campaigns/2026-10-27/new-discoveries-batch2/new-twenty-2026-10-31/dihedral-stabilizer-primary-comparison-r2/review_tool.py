import os,resource,time,json,hashlib,sys,datetime,urllib.request,urllib.error
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
p=Path(__file__).resolve().parent
st=time.monotonic()
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*args,**kwargs): return None
op=urllib.request.build_opener(NoRedirect)
try:
 if sys.argv[1]=='get':
  label,url=sys.argv[2:4]; receipt={'label':label,'url':url,'method':'GET','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  prior=json.loads((p/'HTTP-RECEIPTS.json').read_text()) if (p/'HTTP-RECEIPTS.json').exists() else []
  assert len(prior)<30 and all(r['url']!=url for r in prior)
  try:
   try: response=op.open(urllib.request.Request(url,headers={'User-Agent':'Source-comparison-review/1.0'}),timeout=30)
   except urllib.error.HTTPError as e: response=e
   with response:
    data=response.read(20*1024**2+1); assert len(data)<=20*1024**2
    receipt.update(status=response.status,final_url=response.url,headers=dict(response.headers),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
    (p/(label+'.raw')).write_bytes(data)
  except Exception as e: receipt['error']=repr(e)
  prior.append(receipt);(p/'HTTP-RECEIPTS.json').write_text(json.dumps(prior,indent=2)+'\n');print(json.dumps(receipt,indent=2))
 elif sys.argv[1]=='read':
  path,start,end=sys.argv[2:5];s=Path(path);data=s.read_bytes();t=data.decode();a=int(start);b=int(end)
  reads=json.loads((p/'READ-INVENTORY.json').read_text());reads.append({'path':str(s),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'requested_char_range':[a,b],'scope':'displayed range; not whole-file semantic claim'})
  (p/'READ-INVENTORY.json').write_text(json.dumps(reads,indent=2)+'\n');print(t[a:b])
finally:
 u=resource.getrusage(resource.RUSAGE_SELF)
 with (p/'resources.jsonl').open('a') as f: f.write(json.dumps({'argv':sys.argv[1:],'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit_s':120,'AS_bytes':6*1024**3,'external_wall_timeout_s':140,'wall_s':time.monotonic()-st,'self_cpu_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'telemetry':'self only; group/cgroup/managed service unknown'})+'\n')
