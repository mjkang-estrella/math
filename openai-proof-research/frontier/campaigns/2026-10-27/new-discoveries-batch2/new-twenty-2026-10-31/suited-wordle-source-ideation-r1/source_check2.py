import os,resource,time,json,hashlib,urllib.request,urllib.error,pathlib,datetime,re
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=pathlib.Path(__file__).parent;(p/'http').mkdir(exist_ok=True)
jobs=[('colored-journal','https://link.springer.com/article/10.1007/s11856-007-0065-z'),('successor-current.pdf','https://arxiv.org/pdf/2609.01874'),('aim-readme-current','https://raw.githubusercontent.com/the-omega-institute/trureturing/5a97247bf6ad10485d8891db5430b9e34def4933/README.md'),('aim-commit','https://github.com/the-omega-institute/trureturing/commit/5a97247bf6ad10485d8891db5430b9e34def4933')]
for name,url in jobs:
 t=time.monotonic(); rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as r:b=r.read(4000000);rec.update(status=r.status,final_url=r.url)
 except urllib.error.HTTPError as e:b=e.read(20000);rec.update(status=e.code,error=str(e))
 except Exception as e:b=b'';rec.update(error=str(e))
 (p/'http'/name).write_bytes(b);rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),wall=time.monotonic()-t)
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(name,rec.get('status'),re.findall(r'"currentOid":"([a-f0-9]{40})"',b.decode(errors='replace'))[:1],flush=True)
(p/'source-job2.json').write_text(json.dumps({'pid':os.getpid(),'ended':True,'usage':list(resource.getrusage(resource.RUSAGE_SELF)),'limits':'CPU120 AS6GiB affinity2 outer wall140'},indent=2))
