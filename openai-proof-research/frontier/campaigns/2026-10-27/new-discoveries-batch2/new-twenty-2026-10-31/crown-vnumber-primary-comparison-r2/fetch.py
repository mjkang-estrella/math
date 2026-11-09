from pathlib import Path
import urllib.request,hashlib,json,datetime,time,subprocess
q=Path(__file__).resolve().parent;(q/'http').mkdir(exist_ok=True)
urls=[('older-v1.pdf','https://arxiv.org/pdf/2507.02161v1'),('older-journal.html','https://link.springer.com/article/10.1007/s13348-026-00511-4'),('older.abs','https://arxiv.org/abs/2507.02161'),('newer.abs','https://arxiv.org/abs/2610.18213'),('openai.html','https://github.com/openai/math'),('pool.html','https://github.com/LeanPool/lean-pool'),('omega.html','https://github.com/the-omega-institute/trureturing'),('liwski-author.html','https://www.kuleuven.be/wieiswie/nl/person/00165104')]
for name,url in urls:
 t=time.monotonic();r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=8) as s:
   b=s.read(16*1024**2+1);r.update(status=s.status,final_url=s.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(q/'http'/name).write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None),bytes=0,sha256=None)
 r['wall_s']=time.monotonic()-t
 with (q/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
 if name.endswith('.pdf') and 'error' not in r:
  x=subprocess.run(['pdftotext','-layout',str(q/'http'/name),str(q/'http'/(name+'.txt'))],timeout=30,capture_output=True);print('pdftotext',x.returncode)
