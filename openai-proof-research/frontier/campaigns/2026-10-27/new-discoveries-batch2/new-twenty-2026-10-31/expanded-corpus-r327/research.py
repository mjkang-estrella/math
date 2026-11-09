import os,resource,time,atexit,json,pathlib,sys,hashlib,urllib.request,datetime
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent;t0=time.monotonic()
def log():
 r=resource.getrusage(resource.RUSAGE_SELF)
 with (p/'resources.jsonl').open('a') as f:f.write(json.dumps({'argv':sys.argv,'affinity':sorted(os.sched_getaffinity(0)),'cpu_seconds':r.ru_utime+r.ru_stime,'wall_seconds':time.monotonic()-t0,'self_highwater_KiB':r.ru_maxrss,'group_RSS':'unavailable','reaped':'synchronous process exit'})+'\n')
atexit.register(log)
def fetch(url,name):
 receipt={'url':url,'method':'GET','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source reader'}),timeout=22) as r:
   b=r.read(12000000);receipt.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/'sources').mkdir(exist_ok=True);(p/'sources'/name).write_bytes(b)
 except Exception as e:receipt['error']=str(e)
 with (p/'http.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(json.dumps(receipt))
if __name__=='__main__':
 if sys.argv[1]=='fetch':
  for url,name in zip(sys.argv[2::2],sys.argv[3::2]):fetch(url,name)
