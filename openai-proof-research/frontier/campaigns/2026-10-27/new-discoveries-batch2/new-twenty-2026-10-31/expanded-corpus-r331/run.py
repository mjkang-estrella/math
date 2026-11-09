import os,resource,sys,time,pathlib,json,hashlib,urllib.request,urllib.error,re,datetime
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent; start=time.time(); h=lambda b:hashlib.sha256(b).hexdigest()
def fetch(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat();rec={'url':url,'utc':t,'method':'GET','read_depth':'download only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Public mathematical research source reader'}),timeout=16) as r:
   b=r.read(16000000);rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=h(b));(p/'sources').mkdir(exist_ok=True);(p/'sources'/name).write_bytes(b)
 except Exception as e: rec.update(error=str(e),status=getattr(e,'code',None));b=b''
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec));return b
exitcode=0
try:exec(sys.stdin.read())
except BaseException as e:
 exitcode=1;print(type(e).__name__,str(e));raise
finally:
 with (p/'resource-log.jsonl').open('a') as f:f.write(json.dumps({'job':'runtime stdin','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed':time.time()-start,'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'as_limit':6*1024**3,'self_ru_maxrss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'python_outcome':exitcode,'telemetry_scope':'self only, not process group/cgroup/service'})+'\n')
