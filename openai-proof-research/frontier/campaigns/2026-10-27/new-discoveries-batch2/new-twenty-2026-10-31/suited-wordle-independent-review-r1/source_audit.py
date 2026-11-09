import os,resource,signal,time,json,hashlib,re,urllib.request,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);signal.alarm(140)
p=Path(__file__).resolve().parent;(p/'http').mkdir(exist_ok=True)
urls={'wordle':'https://arxiv.org/abs/2408.00903','successor':'https://arxiv.org/abs/2609.01874','colored':'https://arxiv.org/abs/math/0503238','openai':'https://github.com/openai/math','aim':'https://github.com/the-omega-institute/trureturing','pool':'https://github.com/LeanPool/lean-pool'}
rows=[]
for name,url in urls.items():
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};start=time.monotonic()
 try:
  with urllib.request.urlopen(url,timeout=15) as r:
   data=r.read(3000001);row.update(status=r.status,final_url=r.url)
  if len(data)>3000000:raise ValueError('response cap')
  (p/'http'/name).write_bytes(data);row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  text=data.decode(errors='replace')
  if name in ['openai','aim','pool']:row['head_candidates']=list(dict.fromkeys(re.findall(r'currentOid":"([a-f0-9]{40})',text)))
  else:row['version_lines']=[x for x in text.splitlines() if any(t in x for t in ['[v1]','[v2]','[v3]','Journal reference','journal-ref','Submission history'])]
 except Exception as e:row['error']=str(e)
 row['wall_seconds']=time.monotonic()-start;rows.append(row)
 (p/'http-receipts.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
(p/'source-job.json').write_text(json.dumps({'completed':True,'reaped':'synchronous parent tool','cpu_cap':120,'wall_alarm':140,'address_space':6*1024**3,'affinity':list(os.sched_getaffinity(0)),'rusage':list(resource.getrusage(resource.RUSAGE_SELF))},indent=2))
