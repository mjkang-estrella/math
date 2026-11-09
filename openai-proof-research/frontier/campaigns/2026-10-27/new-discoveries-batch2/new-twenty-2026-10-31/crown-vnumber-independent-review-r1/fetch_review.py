import os,resource,signal,time,json,hashlib,urllib.request,datetime
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3)); signal.alarm(140)
p=Path(__file__).resolve().parent; (p/'http').mkdir(exist_ok=True)
urls={'current.abs':'https://arxiv.org/abs/2507.03889','v1.html':'https://arxiv.org/html/2507.03889v1','v2.html':'https://arxiv.org/html/2507.03889v2','cuts.abs':'https://arxiv.org/abs/2507.02161','latest.abs':'https://arxiv.org/abs/2610.18213','openai.html':'https://github.com/openai/math','pool.html':'https://github.com/LeanPool/lean-pool','omega.html':'https://github.com/the-omega-institute/trureturing'}
for name,url in urls.items():
 r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()); t=time.monotonic()
 try:
  with urllib.request.urlopen(url,timeout=8) as f: data=f.read(16*1024**2+1); r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()); (p/'http'/name).write_bytes(data)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 r['wall_s']=time.monotonic()-t
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
(p/'jobs.jsonl').open('a').write(json.dumps(dict(job='fetch_review.py',status='completed/reaped synchronously',cpu_cap_s=120,wall_cap_s=140,AS_bytes=6*1024**3,cpus=2,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
