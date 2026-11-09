import os,resource,signal,time,pathlib,json,hashlib,datetime,urllib.request,urllib.error,concurrent.futures
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));signal.alarm(140);os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).parent;(p/'http').mkdir(exist_ok=True);r=json.loads((p/'reservation.json').read_text());jobs=[]
jobs=[('crown-v1.html','https://arxiv.org/html/2507.03889v1'),('hamming-v1.html','https://arxiv.org/html/2411.00250v1'),('cyclic-v1.html','https://arxiv.org/html/2404.18847v1'),('cyclic-v2.html','https://arxiv.org/html/2404.18847v2'),('cyclic-v3.html','https://arxiv.org/html/2404.18847v3'),('cyclic-journal.html','https://quantum-journal.org/papers/q-2025-06-04-1763/'),('pool-projects-current.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool/projects.yml'),('openai-CONTENTS-current.md','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/CONTENTS.md'),('omega-readme.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/f6227ace45a0ac2ea7ec151cfdea85b9f104334a/README.md')]
def fetch(job):
 name,url=job;rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};data=b'';start=time.monotonic()
 try:
  with urllib.request.urlopen(url,timeout=6) as f:data=f.read(16000000);rec.update(status=f.status,final_url=f.url)
 except urllib.error.HTTPError as e:data=e.read(100000);rec.update(status=e.code,error=str(e))
 except Exception as e:rec.update(status=None,error=str(e))
 (p/'http'/name).write_bytes(data);rec.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),wall_s=time.monotonic()-start);return rec
start=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for rec in pool.map(fetch,jobs):
  with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec['name'],rec['status'],rec['bytes'],flush=True)
(p/'fetch2-resources.json').write_text(json.dumps({'wall_s':time.monotonic()-start,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'cpus':list(os.sched_getaffinity(0)),'all_joined':True,'cpu_limit':120,'wall_limit':140,'address_limit':6*1024**3}))
