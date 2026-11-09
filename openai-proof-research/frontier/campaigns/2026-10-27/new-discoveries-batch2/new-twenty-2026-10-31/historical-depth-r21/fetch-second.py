from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,resource,os,sys
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
O=Path(__file__).resolve().parent; (O/'sources').mkdir(exist_ok=True)
tasks=[('348788.pdf','https://arxiv.org/pdf/2011.12822'),('342062-published.pdf','https://ajc.maths.uq.edu.au/pdf/85/ajc_v85_p061.pdf'),('348207-successor.pdf','https://math.colgate.edu/~integers/w77/w77.pdf')]
receipts=[]
for name,url in tasks:
 r=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research/1.0'}),timeout=40) as f: b=f.read(16000000);r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  (O/'sources'/name).write_bytes(b);r.update(file=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 receipts.append(r);print(name,r.get('status'),r.get('bytes'),flush=True)
 (O/'sources/receipts-second.json').write_text(json.dumps(receipts,indent=2)+'\n')
