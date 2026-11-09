import os,resource,signal,time,pathlib,json,hashlib,datetime,urllib.request,urllib.error,concurrent.futures
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));signal.alarm(140);os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).parent;(p/'http').mkdir(exist_ok=True);r=json.loads((p/'reservation.json').read_text());jobs=[('350270.html', 'https://arxiv.org/html/2104.00665'), ('375665.html', 'https://arxiv.org/html/2606.30486'), ('375707.html', 'https://arxiv.org/html/2607.00372'), ('376184.html', 'https://arxiv.org/html/2607.20157'), ('376383.html', 'https://arxiv.org/html/2607.27582'), ('370830.html', 'https://arxiv.org/html/2510.06549'), ('362090.html', 'https://arxiv.org/html/2402.18297'), ('362807.html', 'https://arxiv.org/html/2404.12838'), ('363474.html', 'https://arxiv.org/html/2406.06421'), ('363583.html', 'https://arxiv.org/html/2406.12689')]
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
(p/'fetch3-resources.json').write_text(json.dumps({'wall_s':time.monotonic()-start,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'cpus':list(os.sched_getaffinity(0)),'all_joined':True,'cpu_limit':120,'wall_limit':140,'address_limit':6*1024**3}))
