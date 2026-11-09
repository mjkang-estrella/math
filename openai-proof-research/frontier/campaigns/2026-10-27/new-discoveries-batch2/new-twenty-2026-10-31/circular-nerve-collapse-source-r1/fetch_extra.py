import resource,signal,os,json,hashlib,datetime,urllib.request,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));signal.alarm(140)
try: os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
except AttributeError: pass
p=Path(__file__).parent; (p/'sources').mkdir(exist_ok=True)
jobs=[('strong','https://people.kth.se/~jbarmak/strong.pdf'),('random-journal','https://link.springer.com/content/pdf/10.1007/s00454-025-00794-7.pdf')]
with (p/'receipts-extra.jsonl').open('w') as log:
 for name,url in jobs:
  r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=12) as q: data=q.read(16000000);r.update(status=q.status,final_url=q.url)
   f=p/'sources'/name;f.write_bytes(data);r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
   if data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f)+'.txt'],check=True,timeout=15)
  except Exception as e:r['error']=str(e)
  log.write(json.dumps(r)+'\n');log.flush();print(name,r.get('status',r.get('error')),flush=True)
