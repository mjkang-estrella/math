from pathlib import Path
import urllib.request,hashlib,json,datetime,time,subprocess
q=Path(__file__).resolve().parent;(q/'http').mkdir(exist_ok=True)
urls=[('liwski-repository.html','https://lirias.kuleuven.be/handle/20.500.12942/786200'),('kumar-author.html','https://sites.google.com/view/arvkumar/research')]
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
