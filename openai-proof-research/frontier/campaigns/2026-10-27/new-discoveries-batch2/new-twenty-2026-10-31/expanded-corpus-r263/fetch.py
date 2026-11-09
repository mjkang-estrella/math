import json,sys,time,hashlib,resource,subprocess,re,urllib.request,concurrent.futures
from pathlib import Path
from datetime import datetime,timezone
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
r=json.loads((p/'reservation.json').read_text()); jobs=[]
if len(sys.argv)>1:
 jobs=[tuple(x.split('=',1)) for x in sys.argv[1:]]
else:
 for o in r['rows']:
  a=o['source_url'].split('/')[-1]; jobs.extend([(a+'-abs','https://arxiv.org/abs/'+a),(a+'-pdf','https://arxiv.org/pdf/'+a)])
def fetch(job):
 name,url=job; rec={'url':url,'utc':datetime.now(timezone.utc).isoformat(),'name':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=12) as f:
   data=f.read(20000000);rec.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)); out=p/'sources'/name;out.write_bytes(data)
   if data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(out),str(out)+'.txt'],timeout=12,check=True)
 except Exception as e:rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for rec in ex.map(fetch,jobs):
  with (p/'receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec['name'],rec.get('status'),rec.get('error',''),flush=True)
