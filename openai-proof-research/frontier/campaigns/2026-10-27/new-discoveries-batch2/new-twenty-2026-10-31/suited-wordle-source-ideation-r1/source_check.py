import os,resource,time,json,hashlib,urllib.request,urllib.error,pathlib,datetime,re
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=pathlib.Path(__file__).parent;(p/'http').mkdir(exist_ok=True)
jobs=[('wordle-abs','https://arxiv.org/abs/2408.00903'),('successor-abs','https://arxiv.org/abs/2609.01874'),('colored-abs','https://arxiv.org/abs/math/0503238'),('openai','https://github.com/openai/math'),('aim','https://github.com/the-omega-institute/trureturing'),('pool','https://github.com/LeanPool/lean-pool')]
for name,url in jobs:
 t=time.monotonic(); rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as r:b=r.read(4000000);rec.update(status=r.status,final_url=r.url)
 except urllib.error.HTTPError as e:b=e.read(20000);rec.update(status=e.code,error=str(e))
 except Exception as e:b=b'';rec.update(error=str(e))
 (p/'http'/name).write_bytes(b);rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),wall=time.monotonic()-t)
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(name,rec.get('status'),re.findall(r'"currentOid":"([a-f0-9]{40})"',b.decode(errors='replace'))[:1],flush=True)
(p/'source-job.json').write_text(json.dumps({'pid':os.getpid(),'ended':True,'usage':list(resource.getrusage(resource.RUSAGE_SELF)),'limits':'CPU120 AS6GiB affinity2 outer wall140'},indent=2))
